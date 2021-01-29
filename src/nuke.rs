//! Nuclear Data Types

use crate::nk::*;
use crate::nkgc::{PV, Traceable, Arena, SymID};
use crate::compile::Builtin;
use crate::fmt::{LispFmt, VisitSet};
use crate::sym_db::SymDB;
use std::mem;
use std::ptr::drop_in_place;
use std::marker::PhantomData;
use std::ffi;
use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::fmt;
use std::ptr;
use core::fmt::Debug;

macro_rules! with_atom {
    ($item:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match $item.type_of() {
                $(NkT::$t => {
                    let $item = &*$item.fastcast::<$path>();
                    $fn
                }),+
            }
        }
    }
}

macro_rules! with_atom_mut {
    ($item:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match $item.type_of() {
                $(NkT::$t => {
                    let $item = &mut *$item.fastcast_mut::<$path>();
                    $fn
                }),+
            }
        }
    }
}

macro_rules! with_atom_inst {
    ($item:ident, $what:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match $item.type_of() {
                $(NkT::$t => $what::$t({
                    let $item = &mut *$item.fastcast_mut::<$path>();
                    $fn
                })),+
            }
        }
    }
}

macro_rules! fissile_types {
    ($(($t:ident, $sym_type_of:expr, $path:path)),+) => {
        #[derive(Debug)]
        pub enum NkSum { $($t($path)),+ }

        #[repr(u8)]
        #[derive(Debug)]
        pub enum NkT { $($t),+ }

        #[derive(Debug)]
        pub enum NkMut<'a> { $($t(&'a mut $path)),+ }

        #[derive(Debug)]
        pub enum NkRef<'a> { $($t(&'a $path)),+ }

        pub trait Fissile: LispFmt + Debug + Clone + Traceable {
            fn type_of() -> NkT;
        }

        impl From<NkT> for SymID {
            fn from(src: NkT) -> SymID {
                match src { $(NkT::$t => $sym_type_of),+ }
            }
        }

        impl NkRef<'_> {
            pub fn type_of(&self) -> NkT {
                match self { $(Self::$t(..) => NkT::$t ),+ }
            }
        }

        impl NkMut<'_> {
            pub fn type_of(&self) -> NkT {
                match self { $(Self::$t(..) => NkT::$t ),+ }
            }
        }

        impl NkSum {
            pub fn push_to(&self, ar: &mut Arena) {
                match self { $(Self::$t(v) => ar.push_new(v.clone())),+ }
            }
        }

        $(impl From<$path> for NkSum {
            fn from(item: $path) -> Self { NkSum::$t(item) }
        })+

        fn clone_atom(item: &NkAtom) -> NkSum {
            unsafe {
                match item.type_of() {
                    $(NkT::$t => (&*item.fastcast::<$path>()).clone().into()),+
                }
            }
        }

        // FIXME: This uses dynamic dispatch to potentially reduce a little
        //        code-duplication, the problem could also be solved using a
        //        macro-macro (which could be far more general).
        pub fn trace_map_mut<T, F>(atom: &mut NkAtom, f: F) -> T
            where F: Fn(&mut dyn Traceable) -> T {
            with_atom_mut!(atom, { f(atom) },
                           $(($t,$path)),+)
        }

        // TODO: When `if` inside const is stabilized you can make this a const fn,
        //       by calling a recursive const fn min()
        fn minimal_fissile_sz() -> NkSz {
            const LEN: usize = count_args!($($t),+);
            const SIZES: [usize; LEN] = [
                $(mem::size_of::<$path>() /*- mem::align_of::<$path>()*/),+
            ];
            *SIZES.iter().min().unwrap() as NkSz
        }

        const DESTRUCTORS: [unsafe fn (*mut u8); count_args!($($t),+)] = [
            $(|x| { unsafe { drop_in_place(x as *mut $path) } }),+
        ];

        pub fn update_ptr_atom(atom: &mut NkAtom, reloc: &NkRelocArray) {
            with_atom_mut!(atom, {atom.update_ptrs(reloc)},
                           $(($t,$path)),+)
        }

        pub fn mark_atom(atom: &mut NkAtom, gray: &mut Vec<*mut NkAtom>) {
            with_atom_mut!(atom, {atom.trace(gray)}, $(($t,$path)),+);
            atom.set_color(Color::Black)
        }

        fn to_fissile_mut<'a>(atom: *mut NkAtom) -> NkMut<'a> {
            let atom = unsafe { &mut *atom };
            with_atom_inst!(atom, NkMut, {atom}, $(($t,$path)),+)
        }

        fn to_fissile_ref<'a>(atom: *const NkAtom) -> NkRef<'a> {
            // FIXME: with_atom(_inst)! is not flexible enough, it needs to be able
            //        to deal with both &ref and &mut ref. Hence this war crime:
            let atom = unsafe { &mut *(atom as *mut NkAtom) };
            with_atom_inst!(atom, NkRef, {&*atom}, $(($t,$path)),+)
        }

        impl LispFmt for NkAtom {
            fn lisp_fmt(&self,
                        db: &dyn SymDB,
                        visited: &mut VisitSet,
                        f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let p = self as *const NkAtom;
                let atom = self;
                if visited.get(&p).is_some() {
                    write!(f, "(...)")
                } else {
                    visited.insert(p);
                    with_atom!(atom, { atom.lisp_fmt(db, visited, f) },
                               $(($t,$path)),+)
                }
            }
        }

        $(impl Fissile for $path {
            fn type_of() -> NkT { NkT::$t }
        })+
    };
}

fissile_types! {
    (Cons, Builtin::Cons.sym(), crate::nkgc::Cons),
    (Lambda, Builtin::Lambda.sym(), crate::nkgc::Lambda),
    (VLambda, Builtin::Lambda.sym(), crate::nkgc::VLambda),
    (String, Builtin::String.sym(), std::string::String),
    (PV, Builtin::Ref.sym(), crate::nkgc::PV),
    (Vector, Builtin::Vector.sym(), Vec<PV>),
    (Stream, Builtin::Stream.sym(), crate::nkgc::Stream),
    (Subroutine, Builtin::Subr.sym(), Box<dyn crate::subrs::Subr>)
}

#[repr(u8)]
#[derive(Debug, PartialEq, Eq, Copy, Clone, std::hash::Hash)]
pub enum Color {
    White = 0,
    Gray = 1,
    Black = 2,
}

impl PartialEq for PairVoidP {
    fn eq(&self, other: &PairVoidP) -> bool {
        other.fst == self.fst
    }
}

impl Eq for PairVoidP {}

impl PartialOrd for PairVoidP {
    fn partial_cmp(&self, other: &PairVoidP) -> Option<Ordering> {
        self.fst.partial_cmp(&other.fst)
    }
}

impl Ord for PairVoidP {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fst.cmp(&other.fst)
    }
}

impl NkRelocArray {
    pub fn get<T>(&self, orig: *const T) -> *const T {
        let arr: &[PairVoidP] = unsafe { self.elems.as_slice(self.length as usize) };
        let srch = PairVoidP { fst: orig as *mut ffi::c_void,
                               snd: ptr::null_mut::<ffi::c_void>() };
        match arr.binary_search(&srch) {
            Ok(idx) => arr[idx].snd as *const T,
            Err(_) => orig
        }
    }

    pub fn len(&self) -> usize {
        self.length as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl fmt::Display for PairVoidP {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:?} => {:?}", self.fst, self.snd)
    }
}

impl fmt::Display for NkRelocArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let arr: &[PairVoidP] = unsafe { self.elems.as_slice(self.length as usize) };
        write!(f, "[")?;
        for u in arr {
            write!(f, "{}, ", u)?;
        }
        write!(f, "]")
    }
}

impl NkAtom {
    pub fn make_ref<T: Fissile>(p: *mut T) -> PV {
        PV::Ref(NkAtom::make_raw_ref(p))
    }

    pub fn as_sum(&self) -> NkSum {
        clone_atom(self)
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn make_raw_ref<T: Fissile>(p: *mut T) -> *mut NkAtom {
        const DELTA: isize = -(mem::size_of::<NkAtom>() as isize);
        unsafe {
            (p as *mut u8).offset(DELTA) as *mut NkAtom
        }
    }

    #[inline]
    pub unsafe fn fastcast_mut<T>(&mut self) -> *mut T {
        const DELTA: isize = mem::size_of::<NkAtom>() as isize;
        (self as *mut NkAtom as *mut u8).offset(DELTA) as *mut T
    }

    #[inline]
    pub unsafe fn fastcast<T>(&self) -> *const T {
        const DELTA: isize = mem::size_of::<NkAtom>() as isize;
        (self as *const NkAtom as *const u8).offset(DELTA) as *mut T
    }

    pub fn cast<T: Fissile>(&mut self) -> Option<&mut T> {
        let ty = T::type_of() as u8;
        if ty == self.meta.typ() {
            unsafe { Some(&mut*self.fastcast_mut::<T>()) }
        } else {
            None
        }
    }

    #[inline]
    pub fn color(&self) -> Color {
        unsafe { mem::transmute(self.meta.color() as u8) }
    }

    #[inline]
    pub fn match_ref(&self) -> NkRef<'_> {
        to_fissile_ref(self as *const NkAtom)
    }

    #[inline]
    pub fn match_mut(&mut self) -> NkMut<'_> {
        to_fissile_mut(self as *mut NkAtom)
    }

    #[inline]
    pub fn set_color(&mut self, color: Color) {
        unsafe { self.meta.set_color(mem::transmute(color)) }
    }

    #[inline]
    pub fn type_of(&self) -> NkT {
        unsafe { mem::transmute(self.meta.typ() as u8) }
    }
}

type RelocInfo = Option<(*mut Nuke, *const NkRelocArray)>;

impl Nuke {
    pub fn new(sz: usize) -> *mut Nuke {
        unsafe {
            nk_new(sz as u64, minimal_fissile_sz(), 0.90)
        }
    }

    #[inline]
    #[must_use = "Relocation must be confirmed"]
    pub fn compact<'z>(&mut self) -> &'z NkRelocArray  {
        let nkp = self as *mut Nuke;
        unsafe {
            nk_compact(nkp);
            let reloc = nk_check_relocation(nkp);
            debug_assert!(!reloc.is_null());
            &*reloc
        }
    }

    #[inline]
    #[must_use = "Relocation must be confirmed"]
    pub fn sweep_compact<'z>(&mut self) -> &'z NkRelocArray  {
        let nkp = self as *mut Nuke;
        unsafe {
            nk_sweep_compact(nkp);
            let reloc = nk_check_relocation(nkp);
            debug_assert!(!reloc.is_null());
            &*reloc
        }
    }

    pub unsafe fn alloc<T: Fissile>(&mut self) -> (*mut T, RelocInfo) {
        let ty = T::type_of() as u8;
        let nkp = self as *mut Nuke;
        let ptr = nk_alloc(nkp, mem::size_of::<T>() as NkSz, ty) as *mut T;
        if !ptr.is_null() {
            return (ptr, None);
        }
        let nkp = nk_make_room(nkp, Nuke::size_of::<T>() as u64);
        let reloc = nk_check_relocation(nkp);
        assert!(!reloc.is_null(), "Relocation array missing after relocation.");
        let ptr = nk_alloc(nkp, mem::size_of::<T>() as NkSz, ty) as *mut T;
        assert!(!ptr.is_null(), "Unable to fit after nk_make_room");
        (ptr, Some((nkp, reloc)))
    }

    pub unsafe fn fit_bytes(&mut self, num_bytes: usize) -> RelocInfo {
        let nkp = self as *mut Nuke;
        let nkp = nk_make_room(nkp, num_bytes as u64);
        let reloc = nk_check_relocation(nkp);
        if reloc.is_null() {
            None
        } else {
            Some((nkp, reloc))
        }
    }

    #[inline]
    pub fn size_of<T: Fissile>() -> usize {
        mem::size_of::<T>() + mem::size_of::<NkAtom>() /*- mem::align_of::<T>()*/
    }

    #[inline]
    pub unsafe fn fit<T: Fissile>(&mut self, num: usize) -> RelocInfo {
        self.fit_bytes(Nuke::size_of::<T>() * num)
    }

    #[inline]
    pub fn confirm_relocation(&mut self) {
        unsafe { nk_confirm_relocation(self as *mut Nuke) }
    }

    pub fn iter_mut(&mut self) -> NukeIter<'_> {
        let fst = unsafe { nk_head(self as *mut Nuke) };
        NukeIter { item: fst,
                   _phantom: Default::default() }
    }
}

#[no_mangle]
pub unsafe extern "C" fn nk_destroy_atom(p: *mut NkAtom) {
    let ty = (*p).meta.typ() as usize;
    DESTRUCTORS[ty]((*p).fastcast_mut::<u8>());
}

pub struct NukeIter<'a> {
    item: *mut NkAtom,
    _phantom: PhantomData<&'a NkAtom>
}

impl<'a> Iterator for NukeIter<'a> {
    type Item = &'a mut NkAtom;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item.is_null() { return None; }
        unsafe {
            let ret = &mut *self.item;
            let item = &*self.item;
            self.item = item.next;
            Some(ret)
        }
    }
}

impl Drop for Nuke {
    fn drop(&mut self) {
        unsafe {
            nk_destroy(self as *mut Nuke)
        }
    }
}
