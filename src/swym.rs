#![allow(dead_code)]

use core::slice;
use std::collections::{HashSet, hash_set};
use std::sync::atomic::AtomicU32;
use std::{cmp, fmt, iter};
use std::hash::{Hash, self, BuildHasher};
use std::{ptr::NonNull, mem, ptr};
use std::alloc::{Layout, alloc, dealloc};
use std::fmt::Debug;

use fnv::FnvHashSet;
use serde::{Deserialize, Serialize};

use crate::nuke::GcRc;
use crate::nuke::memcpy;

struct Sym {
    rc: GcRc,
    ptr: NonNull<u8>,
    len: usize,
    sz: usize,
}

impl Sym {
    // NOTE: This is for eventually creating &'static Sym. If you use this to
    // create Syms on the heap like in SwymDb, you will be leaking the alloc()
    // because the ref-count is initialized to 2.
    //
    // Either allocate all Syms in bulk on a Vec<Sym>, and then free that later,
    // or store the Syms in a static array.
    pub const fn from_static(st: &'static str) -> Sym {
        let len = st.len();
        Sym {
            ptr: unsafe { NonNull::new_unchecked(st.as_ptr() as *mut u8) },
            rc: GcRc::new(AtomicU32::new(2)),
            len,
            sz: len
        }
    }
}

struct /* Hiiiiiighwaaaay tooo theee */ DangerZone {
    ptr: *const u8,
    len: usize,
}

pub struct SymRef(*mut Sym);

impl SymRef {
    /// This is only intended for R8VM-internal use, where we need the syms to
    /// be Copy, and know that they will not be dropped because the SwymDb is
    /// live for as long as the R8VM is.
    pub(crate) fn id(self) -> SymID {
        let p = self.0;
        drop(self);
        SymID(p)
    }
}

impl Into<String> for SymRef {
    fn into(self) -> String {
        unsafe {
            let p = self.0;
            mem::forget(self);
            take_inner_string(p)
        }
    }
}

impl AsRef<str> for SymRef {
    fn as_ref(&self) -> &str {
        unsafe {
            let p = (*self.0).ptr;
            let slice = slice::from_raw_parts(p.as_ptr(), (*self.0).len);
            std::str::from_utf8_unchecked(slice)
        }
    }
}

impl AsRef<str> for SymID {
    fn as_ref(&self) -> &str {
        unsafe {
            let p = (*self.0).ptr;
            let slice = slice::from_raw_parts(p.as_ptr(), (*self.0).len);
            std::str::from_utf8_unchecked(slice)
        }
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Copy)]
pub(crate) struct SymID(*mut Sym);

impl Debug for SymID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        debug_print_sym(self.0, f)
    }
}

impl PartialOrd for SymID {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymID {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_ref().cmp(other.as_ref())
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
        let slice = slice::from_raw_parts((*sym).ptr.as_ptr(), (*sym).len);
        write!(f, "{}", std::str::from_utf8_unchecked(slice))
    }
}

impl Debug for SymRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> fmt::Result {
        debug_print_sym(self.0, f)
    }
}

#[derive(Clone)]
pub struct SymKeyRef(SymRef);

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
            let p = (*self.0.0).ptr.as_ptr();
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
            let l = (*self.0.0).ptr.as_ptr();
            let r = (*other.0.0).ptr.as_ptr();
            let l_len = (*self.0.0).len;
            let r_len = (*other.0.0).len;
            slice::from_raw_parts(l, l_len) == slice::from_raw_parts(r, r_len)
        }
    }
}

impl Eq for SymKeyRef {}

unsafe fn take_inner_string(p: *mut Sym) -> String {
    let layout = Layout::from_size_align_unchecked(
        mem::size_of::<Sym>(),
        mem::align_of::<Sym>(),
    );
    if (*p).rc.is_owned() {
        let s = String::from_raw_parts((*p).ptr.as_ptr(), (*p).len, (*p).sz);
        dealloc(p as *mut u8, layout);
        s
    } else {
        let buf = alloc(Layout::array::<u8>((*p).len).unwrap());
        memcpy(buf, (*p).ptr.as_ptr(), (*p).len);
        let s = String::from_raw_parts(buf, (*p).len, (*p).len);
        (*p).rc.is_dropped();
        s
    }
}

impl Drop for SymRef {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::from_size_align_unchecked(
                mem::size_of::<Sym>(),
                mem::align_of::<Sym>(),
            );
            if (*self.0).rc.is_dropped() {
                drop(String::from_raw_parts((*self.0).ptr.as_ptr(),
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

impl<H> Into<HashSet<String, H>> for SwymDb
    where HashSet<String, H>: Default,
          H: BuildHasher
{
    fn into(self) -> HashSet<String, H> {
        let mut hm: HashSet<String, H> = Default::default();
        for r in self.into_iter() {
            hm.insert(r.into());
        }
        hm
    }
}

impl IntoIterator for SwymDb {
    type Item = SymRef;
    type IntoIter = iter::Map<hash_set::IntoIter<SymKeyRef>,
                              fn(SymKeyRef) -> SymRef>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter().map(|s| s.into_inner())
    }
}

impl SwymDb {
    pub fn put(&mut self, s: String) -> SymRef {
        unsafe {
            let mut s = mem::ManuallyDrop::new(s);

            let mut sym = Sym {
                ptr: NonNull::new(s.as_mut_ptr()).unwrap(),
                len: s.len(),
                sz: s.capacity(),
                rc: GcRc::new(AtomicU32::new(0))
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
            ptr: NonNull::new(s.as_ptr() as *mut u8).unwrap(),
            len: s.len(),
            sz: 0,
            rc: GcRc::new(AtomicU32::new(0))
        };
        let key = mem::ManuallyDrop::new(
            SymKeyRef(SymRef((&mut sym) as *mut Sym))
        );
        if let Some(v) = self.map.get(&key) {
            v.clone_inner()
        } else {
            let mut s = mem::ManuallyDrop::new(s.to_string());
            sym.ptr = NonNull::new(s.as_mut_ptr()).unwrap();
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
        for _ in 0..1000 {
            let ayy_n = swym.put("ayy".to_string());
            assert_eq!(ayy_n, ayy);
        }
        for _ in 0..100 {
            let lmao_n = swym.put("lmao".to_string());
            assert_eq!(lmao1, lmao_n);
        }
    }

    #[test]
    fn go_for_a_swym_and_clone_myself_into_a_hashset() {
        let mut swym = SwymDb::default();
        let lmao1 = swym.put("lmao".to_string());
        let ayy = swym.put("ayy".to_string());
        let lmao2 = swym.put("lmao".to_string());
        assert_eq!(lmao1, lmao2);
        assert_eq!(lmao1.0, lmao2.0);
        for _ in 0..1000 {
            let ayy_n = swym.put("ayy".to_string());
            assert_eq!(ayy_n, ayy);
        }
        for _ in 0..100 {
            let lmao_n = swym.put("lmao".to_string());
            assert_eq!(lmao1, lmao_n);
        }

        let (p_ayy, p_lmao) = unsafe { ((*ayy.0).ptr.as_ptr(),
                                        (*lmao1.0).ptr.as_ptr()) };

        let hm: FnvHashSet<String> = swym.into();

        let mut hm_cmp = FnvHashSet::default();
        hm_cmp.insert(String::from("ayy"));
        hm_cmp.insert(String::from("lmao"));
        assert_eq!(hm, hm_cmp);

        // swym.into() should allocate new Strings, because ayy/lmao are still
        // referenced.
        assert_ne!((*hm.get("ayy").unwrap()).as_ptr(), p_ayy);
        assert_ne!((*hm.get("lmao").unwrap()).as_ptr(), p_lmao);
    }

    #[test]
    fn go_for_a_swym_and_jump_right_into_a_hashset() {
        let mut swym = SwymDb::default();
        let (p_ayy, p_lmao) = {
            let lmao1 = swym.put("lmao".to_string());
            let ayy = swym.put("ayy".to_string());
            let lmao2 = swym.put("lmao".to_string());
            assert_eq!(lmao1, lmao2);
            assert_eq!(lmao1.0, lmao2.0);
            for _ in 0..1000 {
                let ayy_n = swym.put("ayy".to_string());
                assert_eq!(ayy_n, ayy);
            }
            for _ in 0..100 {
                let lmao_n = swym.put("lmao".to_string());
                assert_eq!(lmao1, lmao_n);
            }
            unsafe { ((*ayy.0).ptr.as_ptr(),
                      (*lmao1.0).ptr.as_ptr()) }
        };

        let hm: FnvHashSet<String> = swym.into();

        let mut hm_cmp = FnvHashSet::default();
        hm_cmp.insert(String::from("ayy"));
        hm_cmp.insert(String::from("lmao"));
        assert_eq!(hm, hm_cmp);

        // Confirm that we have the same exact String allocations as we started
        // with.
        assert_eq!((*hm.get("ayy").unwrap()).as_ptr(), p_ayy);
        assert_eq!((*hm.get("lmao").unwrap()).as_ptr(), p_lmao);
    }


    #[test]
    fn hopefully_dont_take_a_hike() {
        let mut swym = SwymDb::default();
        let lmao1 = swym.put_ref("lmao");
        let ayy = swym.put_ref("ayy");
        let lmao2 = swym.put_ref("lmao");
        assert_eq!(lmao1, lmao2);
        assert_eq!(lmao1.0, lmao2.0);
        for _ in 0..1000 {
            let ayy_n = swym.put_ref("ayy");
            assert_eq!(ayy_n, ayy);
        }
        for _ in 0..100 {
            let lmao_n = swym.put_ref("lmao");
            assert_eq!(lmao1, lmao_n);
        }
    }
}
