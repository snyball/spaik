#![allow(dead_code)]

use core::slice;
use std::{cmp, fmt};
use std::hash::{Hash, self};
use std::{ptr::NonNull, mem, ptr};
use std::alloc::{Layout, alloc, dealloc};
use std::fmt::Debug;

use fnv::FnvHashSet;
use serde::{Deserialize, Serialize};

use crate::raw::nuke::GcRc;

struct Sym {
    rc: GcRc,
    ptr: Option<NonNull<u8>>,
    len: usize,
    sz: usize,
}

struct /* Hiiiiiighwaaaay tooo theee */ DangerZone {
    ptr: *const u8,
    len: usize,
}

pub struct SymRef(*mut Sym);

impl SymRef {
    pub(crate) fn id(self) -> SymID {
        let p = self.0;
        drop(self);
        SymID(p)
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Copy)]
pub(crate) struct SymID(*mut Sym);

impl Debug for SymID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        debug_print_sym(self.0, f)
    }
}

impl SymID {
    fn as_str(&self) -> Option<&str> {
        unsafe {
            (*self.0).ptr.map(|p| {
                let slice = slice::from_raw_parts(p.as_ptr(), (*self.0).len);
                std::str::from_utf8_unchecked(slice)
            })
        }
    }
}

impl PartialOrd for SymID {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymID {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let l = self.as_str();
        let r = other.as_str();
        match (l, r) {
            (None, None) => cmp::Ordering::Equal,
            (None, Some(_)) => cmp::Ordering::Less,
            (Some(_), None) => cmp::Ordering::Greater,
            (Some(l), Some(r)) => l.cmp(r),
        }
    }
}

impl<'de> Deserialize<'de> for SymID {
    fn deserialize<D>(_d: D) -> Result<Self, D::Error>
    where D: serde::Deserializer<'de> {
        todo!()
    }
}

impl Serialize for SymID {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        todo!()
    }
}

fn debug_print_sym(sym: *mut Sym, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
    unsafe {
        if let Some(p) = (*sym).ptr {
            let slice = slice::from_raw_parts(p.as_ptr(), (*sym).len);
            write!(f, "{}", std::str::from_utf8_unchecked(slice))
        } else {
            write!(f, "<β>::{}", sym as usize)
        }
    }
}

impl Debug for SymRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        debug_print_sym(self.0, f)
    }
}

#[derive(Clone)]
struct SymKeyRef(SymRef);

impl SymKeyRef {
    pub fn into_inner(self) -> SymRef {
        self.0
    }

    pub fn clone_inner(&self) -> SymRef {
        self.0.clone()
    }

    pub fn disarm(self) {
        mem::forget(self);
    }
}

impl Clone for SymRef {
    fn clone(&self) -> Self {
        unsafe { (*self.0).rc.inc() }
        Self(self.0)
    }
}

impl SymRef {
    unsafe fn new(from: *mut Sym) -> Self {
        unsafe {
            (*from).rc.inc();
            Self(from)
        }
    }
}

impl Hash for SymKeyRef {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        unsafe {
            let Some(p) = (*self.0.0).ptr.map(|p| p.as_ptr()) else { return };
            let len = (*self.0.0).len;
            for i in 0..len {
                (*p.add(i)).hash(state);
            }
        }
    }
}

impl PartialEq for SymRef {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for SymRef {}

impl PartialEq for SymKeyRef {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let Some(l) = (*self.0.0).ptr.map(|p| p.as_ptr()) else { return false };
            let Some(r) = (*other.0.0).ptr.map(|p| p.as_ptr()) else { return false };
            let l_len = (*self.0.0).len;
            let r_len = (*other.0.0).len;
            slice::from_raw_parts(l, l_len) == slice::from_raw_parts(r, r_len)
        }
    }
}

impl Eq for SymKeyRef {}

impl Drop for SymRef {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::from_size_align_unchecked(
                mem::size_of::<Sym>(),
                mem::align_of::<Sym>(),
            );
            if (*self.0).rc.is_dropped() {
                let Some(ptr) = (*self.0).ptr else {
                    dealloc(self.0 as *mut u8, layout);
                    return
                };
                drop(String::from_raw_parts(ptr.as_ptr(),
                                            (*self.0).len,
                                            (*self.0).sz));
                dealloc(self.0 as *mut u8, layout)
            }
        }
    }
}

#[derive(Default)]
pub struct SwymDb {
    map: FnvHashSet<SymKeyRef>,
}

impl Debug for SwymDb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SwymDb").field("map", &"...").finish()
    }
}

impl Drop for SwymDb {
    fn drop(&mut self) {
        for elem in self.map.drain() {
            drop(elem.into_inner())
        }
    }
}

impl SwymDb {
    pub fn put(&mut self, s: String) -> SymRef {
        unsafe {
            let mut s = mem::ManuallyDrop::new(s);

            let mut sym = Sym {
                ptr: NonNull::new(s.as_mut_ptr()),
                len: s.len(),
                sz: s.capacity(),
                rc: GcRc::new(0)
            };

            let key = mem::ManuallyDrop::new(
                SymKeyRef(SymRef((&mut sym) as *mut Sym))
            );
            if let Some(v) = self.map.get(&key) {
                drop(String::from_raw_parts(s.as_mut_ptr(),
                                            s.len(),
                                            s.capacity()));
                v.clone_inner()
            } else {
                let layout = Layout::for_value(&sym);
                let p = alloc(layout) as *mut Sym;
                ptr::write(p, sym);
                let sym = SymRef::new(p);
                self.map.insert(SymKeyRef(sym.clone()));
                sym
            }
        }
    }

    pub fn put_ref(&mut self, s: &str) -> SymRef {
        let mut sym = Sym {
            ptr: NonNull::new(s.as_ptr() as *mut u8),
            len: s.len(),
            sz: 0,
            rc: GcRc::new(0)
        };
        let key = mem::ManuallyDrop::new(
            SymKeyRef(SymRef((&mut sym) as *mut Sym))
        );
        if let Some(v) = self.map.get(&key) {
            v.clone_inner()
        } else {
            let mut s = mem::ManuallyDrop::new(s.to_string());
            sym.ptr = NonNull::new(s.as_mut_ptr());
            sym.sz = s.capacity();
            let layout = Layout::for_value(&sym);
            unsafe {
                let p = alloc(layout) as *mut Sym;
                ptr::write(p, sym);
                let sym = SymRef::new(p);
                self.map.insert(SymKeyRef(sym.clone()));
                sym
            }
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn go_for_a_swym() {
        let mut swym = SwymDb::default();
        let lmao1 = swym.put("lmao".to_string());
        let ayy = swym.put("ayy".to_string());
        let lmao2 = swym.put("lmao".to_string());
        assert_eq!(lmao1, lmao2);
        assert_eq!(lmao1.0, lmao2.0);
        for i in 0..1000 {
            let ayy_n = swym.put("ayy".to_string());
            assert_eq!(ayy_n, ayy);
        }
        for i in 0..100 {
            let lmao_n = swym.put("lmao".to_string());
            assert_eq!(lmao1, lmao_n);
        }
    }

    #[test]
    fn hopefully_dont_take_a_hike() {
        let mut swym = SwymDb::default();
        let lmao1 = swym.put_ref("lmao");
        let ayy = swym.put_ref("ayy");
        let lmao2 = swym.put_ref("lmao");
        assert_eq!(lmao1, lmao2);
        assert_eq!(lmao1.0, lmao2.0);
        for i in 0..1000 {
            let ayy_n = swym.put_ref("ayy");
            assert_eq!(ayy_n, ayy);
        }
        for i in 0..100 {
            let lmao_n = swym.put_ref("lmao");
            assert_eq!(lmao1, lmao_n);
        }
    }
}
