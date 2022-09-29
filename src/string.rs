use std::{alloc::Layout, mem::{size_of, align_of}, fmt};
use std::alloc::{alloc, dealloc, realloc};

use crate::{nuke::{GcRc, memcpy, NkAtom, PtrMap}, fmt::{LispFmt, VisitSet}, nkgc::Traceable, SymDB};

#[repr(C)]
pub struct RcStr {
    rc: GcRc,
    len: u32,
}

impl RcStr {
    pub unsafe fn layout_with(len: usize) -> Layout {
        Layout::from_size_align_unchecked(
            size_of::<RcStr>() + len, align_of::<RcStr>()
        )
    }

    pub unsafe fn layout(&self) -> Layout {
        Self::layout_with(self.len as usize)
    }

    pub unsafe fn buffer(&mut self) -> *mut u8 {
        (self as *const RcStr as *mut u8).offset(size_of::<RcStr>() as isize)
    }
}

pub struct StrBuilder {
    s: *mut RcStr,
    sz: usize,
}

impl StrBuilder {
    pub fn new(sz: usize) -> Self {
        unsafe {
            let layout = RcStr::layout_with(sz);
            let s = alloc(layout) as *mut RcStr;
            Self { s, sz }
        }
    }

    pub fn push_char(&mut self, c: char) {
        unsafe {
            let len = (*self.s).len as usize;
            if len + 4 > self.sz {
                self.sz = (self.sz * 2).min(4);
                self.s = realloc(self.s as *mut u8,
                                 RcStr::layout_with(self.sz),
                                 1) as *mut RcStr;
            }
            let dst = std::slice::from_raw_parts_mut(
                (*self.s).buffer().add(len), 4);
            let s = c.encode_utf8(dst);
            (*self.s).len += s.len() as u32;
        }
    }

    pub fn push(&mut self, s: impl AsRef<str>) {
        unsafe {
            let s = s.as_ref();
            let len = (*self.s).len as usize;
            (*self.s).len += s.len() as u32;
            if (*self.s).len as usize > self.sz {
                self.sz = (self.sz * 2).min((*self.s).len as usize);
                self.s = realloc(self.s as *mut u8,
                                 RcStr::layout_with(self.sz),
                                 1) as *mut RcStr;
            }
            memcpy((*self.s).buffer().add(len), s.as_ptr(), len);
        }
    }

    pub fn fit(self) -> *mut RcStr {
        unsafe {
            (*self.s).rc.inc();
            let len = (*self.s).len as usize;
            if self.sz == len {
                self.s
            } else {
                realloc(self.s as *mut u8,
                        RcStr::layout_with(len),
                        1) as *mut RcStr
            }
        }
    }

    pub fn done(self) -> *mut RcStr {
        unsafe { (*self.s).rc.inc() }
        self.s
    }
}

// TODO: Replace the String type with this
#[derive(Debug)]
pub struct Str(*mut RcStr);

impl AsRef<str> for Str {
    fn as_ref(&self) -> &str {
        unsafe {
            let v = std::slice::from_raw_parts(
                (self.0 as *const RcStr as *const u8)
                    .offset(size_of::<RcStr>() as isize),
                (*self.0).len as usize
            );
            std::str::from_utf8_unchecked(v)
        }
    }
}

impl Traceable for Str {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {}
    fn update_ptrs(&mut self, reloc: &PtrMap) {}
}

impl LispFmt for Str {
    fn lisp_fmt(&self,
                _db: &dyn SymDB,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

impl Clone for Str {
    fn clone(&self) -> Self {
        unsafe { (*self.0).rc.inc() }
        Self(self.0.clone())
    }
}

impl Drop for Str {
    fn drop(&mut self) {
        unsafe {
            if (*self.0).rc.is_dropped() {
                dealloc(self.0 as *mut u8, (*self.0).layout())
            }
        }
    }
}
