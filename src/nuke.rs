/*!
 * The Nuclear Allocator
 */

use crate::error::Error;
use crate::nkgc::{PV, Traceable, Arena, SymID, GCStats};
use crate::compile::Builtin;
use crate::fmt::{LispFmt, VisitSet};
use crate::sym_db::{SymDB, SYM_DB};
use core::slice;
use std::any::TypeId;
use std::mem::{self, size_of};
use std::ptr::{drop_in_place, self};
use std::marker::PhantomData;
use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::fmt;
use core::fmt::Debug;
#[cfg(not(target_arch = "wasm32"))]
use std::time::SystemTime;

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
        #[derive(Debug, PartialEq, Eq)]
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

        #[inline]
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
        #[inline]
        pub fn trace_map_mut<T, F>(atom: &mut NkAtom, f: F) -> T
            where F: Fn(&mut dyn Traceable) -> T
        {
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

        #[inline]
        pub fn update_ptr_atom(atom: &mut NkAtom, reloc: &PtrMap) {
            with_atom_mut!(atom, {atom.update_ptrs(reloc)},
                           $(($t,$path)),+)
        }

        #[inline]
        pub fn mark_atom(atom: &mut NkAtom, gray: &mut Vec<*mut NkAtom>) {
            with_atom_mut!(atom, {atom.trace(gray)}, $(($t,$path)),+);
            atom.set_color(Color::Black)
        }

        #[inline]
        fn to_fissile_mut<'a>(atom: *mut NkAtom) -> NkMut<'a> {
            let atom = unsafe { &mut *atom };
            with_atom_inst!(atom, NkMut, {atom}, $(($t,$path)),+)
        }

        #[inline]
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

trait Fuse: Fissile {
}

pub trait CloneIterator: Iterator {
    fn clone_box(&self) -> Box<dyn CloneIterator<Item = Self::Item>>;
}

impl<T> CloneIterator for T
where
    T: 'static + Iterator + Clone,
{
    fn clone_box(&self) -> Box<dyn CloneIterator<Item = Self::Item>> {
        Box::new(self.clone())
    }
}

pub struct Iter {
    root: PV,
    it: Box<dyn CloneIterator<Item = PV>>
}

impl Iter {
    pub fn new(root: PV, it: Box<dyn CloneIterator<Item = PV>>) -> Iter {
        Iter { root, it }
    }
}

impl Clone for Iter {
    fn clone(&self) -> Self {
        Self { root: self.root.clone(),
               it: self.it.clone_box() }
    }
}

impl fmt::Debug for Iter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Iter")
         .field("root", &self.root)
         .field("it", &"...")
         .finish()
    }
}

impl Traceable for Iter {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        self.root.trace(gray)
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        self.root.update_ptrs(reloc)
    }
}

impl LispFmt for Iter {
    fn lisp_fmt(&self,
                db: &dyn SymDB,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Iterator for Iter {
    type Item = PV;

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next()
    }
}

#[derive(Clone)]
pub struct Object {
    type_id: TypeId,
    trace_fnp: unsafe fn(*const u8, gray: &mut Vec<*mut NkAtom>),
    update_ptrs_fnp: unsafe fn(*mut u8, reloc: &PtrMap),
    destructor_fnp: unsafe fn(*mut u8),
    lisp_fmt_fnp: unsafe fn(*const u8, db: &dyn SymDB, visited: &mut VisitSet, f: &mut fmt::Formatter<'_>) -> fmt::Result,
    debug_fmt_fnp: unsafe fn(*const u8, f: &mut fmt::Formatter<'_>) -> fmt::Result,
    mem: Vec<u8>,
}

impl Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Object {{ ")?;
        unsafe {
            (self.debug_fmt_fnp)(self.mem.as_ptr(), f)?;
        }
        write!(f, " }}")?;
        Ok(())
    }
}

impl LispFmt for Object {
    fn lisp_fmt(&self, db: &dyn SymDB, visited: &mut VisitSet, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe {
            (self.lisp_fmt_fnp)(self.mem.as_ptr(), db, visited, f)
        }
    }
}

impl Object {
    pub fn new<T: Fissile + 'static>(obj: T) -> Object {
        let mut mem: Vec<u8> = Vec::with_capacity(size_of::<T>());
        unsafe {
            ptr::copy_nonoverlapping(&obj as *const T as *const u8,
                                     mem.as_mut_ptr(),
                                     size_of::<T>())
        }
        Object {
            type_id: TypeId::of::<T>(),
            trace_fnp: |obj, gray| {
                let obj = unsafe { &*( obj as *const T ) };
                obj.trace(gray)
            },
            update_ptrs_fnp: |obj, reloc| {
                let obj = unsafe { &mut*( obj as *mut T ) };
                obj.update_ptrs(reloc)
            },
            destructor_fnp: |obj| {
                unsafe {
                    drop_in_place(obj as *mut T)
                }
            },
            lisp_fmt_fnp: |obj, db, visited, f| -> fmt::Result {
                let obj = unsafe { &mut*( obj as *mut T ) };
                obj.lisp_fmt(db, visited, f)
            },
            debug_fmt_fnp: |obj, f| -> fmt::Result {
                let obj = unsafe { &mut*( obj as *mut T ) };
                obj.fmt(f)
            },
            mem
        }
    }

    pub fn cast<T: Fissile + 'static>(&self) -> Result<&T, Error> {
        let id = TypeId::of::<T>();
        if id != self.type_id {
            // FIXME: Better error
            return err!(SomeError, msg: String::from("Object cast error"))
        }
        let ptr = self.mem.as_ptr();
        Ok(unsafe {
            &*(ptr as *const T)
        })
    }

    pub unsafe fn fastcast_mut<T: Fissile + 'static>(&mut self) -> &mut T {
        let ptr = self.mem.as_mut_ptr();
        &mut*(ptr as *mut T)
    }

    pub fn cast_mut<T: Fissile + 'static>(&mut self) -> Result<&mut T, Error> {
        let id = TypeId::of::<T>();
        if id != self.type_id {
            // FIXME: Better error
            return err!(SomeError, msg: String::from("Object cast error"))
        }
        Ok(unsafe { self.fastcast_mut() })
    }
}

impl Traceable for Object {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        unsafe {
            (self.trace_fnp)(self.mem.as_ptr(), gray);
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        unsafe {
            (self.update_ptrs_fnp)(self.mem.as_mut_ptr(), reloc);
        }
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        unsafe {
            (self.destructor_fnp)(self.mem.as_mut_ptr());
        }
    }
}

fissile_types! {
    (Cons, Builtin::Cons.sym(), crate::nkgc::Cons),
    (Lambda, Builtin::Lambda.sym(), crate::nkgc::Lambda),
    (VLambda, Builtin::Lambda.sym(), crate::nkgc::VLambda),
    (String, Builtin::String.sym(), std::string::String),
    (PV, Builtin::Ref.sym(), crate::nkgc::PV),
    (Vector, Builtin::Vector.sym(), Vec<PV>),
    (Stream, Builtin::Stream.sym(), crate::nkgc::Stream),
    (Struct, Builtin::Struct.sym(), crate::nuke::Object),
    (Iter, Builtin::Struct.sym(), crate::nuke::Iter),
    (Subroutine, Builtin::Subr.sym(), Box<dyn crate::subrs::Subr>)
}

#[repr(u8)]
#[derive(Debug, PartialEq, Eq, Copy, Clone, std::hash::Hash)]
pub enum Color {
    White = 0,
    Gray = 1,
    Black = 2,
}

impl fmt::Display for PtrPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:?} => {:?}", self.fst, self.snd)
    }
}

impl fmt::Display for PtrMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "[")?;
        for u in self.0.iter() {
            write!(f, "{}, ", u)?;
        }
        write!(f, "]")
    }
}

impl NkAtom {
    #[inline]
    pub unsafe fn destroy(&mut self) {
        DESTRUCTORS[self.meta.typ() as usize](self.fastcast_mut::<u8>());
    }

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

    pub fn raw(&self) -> &[u8] {
        const DELTA: isize = mem::size_of::<NkAtom>() as isize;
        unsafe {
            let p = (self as *const NkAtom as *const u8).offset(DELTA);
            slice::from_raw_parts(p, self.sz as usize)
        }
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

    pub fn full_size(&self) -> usize {
        mem::size_of::<NkAtom>() + self.sz as usize
    }
}

#[allow(dead_code)]
pub struct Nuke {
    free: *mut u8,
    grow_num: usize,
    used: usize,
    num_frees: usize,
    num_allocs: usize,
    num_atoms: usize,
    load_factor: f64,
    load_max: usize,
    min_block_sz: NkSz,
    sz: usize,
    reloc: PtrMap,
    last: *mut NkAtom,
    mem: Vec<u8>,
    #[cfg(not(target_arch = "wasm32"))]
    start_time: SystemTime,
}

fn align<T>(p: *mut T, a: isize) -> *mut T {
    (((p as isize) + a - 1) & !(a - 1)) as *mut T
}

#[inline(always)]
pub unsafe fn memcpy<R, W>(dst: *mut W, src: *const R, sz: usize) {
    ptr::copy_nonoverlapping(src as *const u8, dst as *mut u8, sz);
}

#[allow(dead_code)]
#[inline(always)]
pub unsafe fn memmove<R, W>(dst: *mut W, src: *const R, sz: usize) {
    ptr::copy(src as *const u8, dst as *mut u8, sz);
}

#[cfg(target_pointer_width = "32")]
const ALIGNMENT: isize = 4;
#[cfg(target_pointer_width = "64")]
const ALIGNMENT: isize = 8;

pub struct RelocateToken {
    p: PhantomData<u8>,
}

impl RelocateToken {
    fn new() -> RelocateToken {
        RelocateToken { p: Default::default() }
    }
}

impl Nuke {
    pub fn new(sz: usize) -> Nuke {
        let load_factor = 0.90;
        let min_block_sz = minimal_fissile_sz();

        assert!(min_block_sz > 0, "Minimum allocation size cannot be 0.");
        assert!(sz >= 128, "Nuke too small");
        assert!((0.5..1.0).contains(&load_factor),
               "Load factor outside of [0.5, 1.0) range.");

        let mut nk = Nuke {
            free: ptr::null_mut(),
            grow_num: sz,
            used: 0,
            num_frees: 0,
            num_allocs: 0,
            num_atoms: 0,
            load_factor,
            load_max: (load_factor * sz as f64) as usize,
            min_block_sz,
            sz,
            reloc: PtrMap(Vec::new()),
            last: ptr::null_mut(),
            mem: Vec::with_capacity(sz),
            #[cfg(not(target_arch = "wasm32"))]
            start_time: SystemTime::now(),
        };

        unsafe { nk.mem.set_len(sz) }
        nk.last = nk.fst();
        nk.free = nk.offset(mem::size_of::<NkAtom>());
        nk.used = mem::size_of::<NkAtom>();
        unsafe {
            (*nk.fst()).set_color(Color::Black);
            (*nk.fst()).meta.set_typ(0);
            (*nk.fst()).next = ptr::null_mut();
            (*nk.fst()).sz = 0;
        }
        nk.num_atoms = 1;

        nk
    }

    #[must_use = "Relocation must be confirmed"]
    pub unsafe fn compact(&mut self) -> RelocateToken {
        let mut node = self.fst();
        let mut npos;
        let mut start = self.offset::<u8>(0);

        loop {
            let next_node = (*node).next;
            npos = start as *mut NkAtom;
            let sz = mem::size_of::<NkAtom>() + (*node).sz as usize;
            if npos != node {
                self.reloc.push(node, npos);
                memcpy(npos, node, sz);
            }
            start = align(start.add(sz), ALIGNMENT);
            if next_node.is_null() {
                break;
            } else {
                (*npos).next = start as *mut NkAtom;
                node = next_node;
            }
        }

        self.last = npos;
        self.free = start;

        RelocateToken::new()
    }

    #[must_use = "Relocation must be confirmed"]
    pub unsafe fn sweep_compact(&mut self) -> RelocateToken {
        let mut node = self.fst();
        let mut npos;
        let mut start = self.offset::<u8>(0);

        loop {
            let next_node = {
                let mut num_frees = 0;
                let mut n = (*node).next;
                while !n.is_null() {
                    if (*n).color() == Color::White {
                        (*n).destroy();
                        self.used -= (*n).full_size();
                        num_frees += 1;
                    } else {
                        break;
                    }
                    n = (*n).next;
                }
                self.num_atoms -= num_frees;
                self.num_frees += num_frees;
                n
            };

            let sz = (*node).full_size();
            npos = start as *mut NkAtom;

            if npos != node {
                self.reloc.push(node, npos);
                memcpy(npos, node, sz);
            }

            (*npos).set_color(Color::White);
            start = align(start.add(sz), ALIGNMENT);

            if next_node.is_null() {
                (*npos).next = ptr::null_mut();
                break;
            } else {
                (*npos).next = start as *mut NkAtom;
                node = next_node;
            }
        }

        self.last = npos;
        (*self.fst()).set_color(Color::Black);
        self.free = start;

        RelocateToken::new()
    }

    #[must_use = "Relocation must be confirmed"]
    pub unsafe fn grow(&mut self, fit: usize) -> RelocateToken {
        let new_sz = (self.sz << 1).max(self.sz + fit);
        self.sz = new_sz;
        self.load_max = (self.load_factor * self.sz as f64) as usize;

        let mut used = 0;
        let mut num_atoms = 0;

        let mut new_vec: Vec<u8> = Vec::with_capacity(new_sz);
        #[allow(clippy::uninit_vec)]
        new_vec.set_len(new_sz);
        let mut mem = new_vec.as_mut_ptr();
        let mut new_node = ptr::null_mut();
        let mut node = self.fst();
        while !node.is_null() {
            let sz = (*node).full_size();
            memcpy(mem, node, sz);
            self.reloc.push(node, mem);
            new_node = mem as *mut NkAtom;
            mem = align(mem.add(sz), ALIGNMENT);
            (*new_node).next = mem as *mut NkAtom;
            node = (*node).next;

            used += sz;
            num_atoms += 1;
        }

        self.free = mem;
        (*new_node).next = ptr::null_mut();
        self.last = new_node;
        self.mem = new_vec;

        debug_assert!(num_atoms == self.num_atoms, "Number of atoms did not match");
        debug_assert!(used == self.used, "Usage count did not match");

        RelocateToken::new()
    }

    #[must_use = "Relocation must be confirmed"]
    pub unsafe fn make_room(&mut self, fit: usize) -> RelocateToken {
        if self.used + fit > self.load_max {
            self.grow(fit)
        } else {
            self.compact()
        }
    }

    pub fn confirm_relocation(&mut self, t: RelocateToken) {
        drop(t);
        self.reloc.0.clear();
    }

    pub fn fst(&mut self) -> *mut NkAtom {
        self.mem.as_mut_ptr() as *mut NkAtom
    }

    pub fn offset<T>(&mut self, n: usize) -> *mut T {
        unsafe {
            self.mem.as_mut_ptr().add(n) as *mut T
        }
    }

    #[must_use = "Relocation must be confirmed"]
    pub unsafe fn alloc<T: Fissile>(&mut self) -> (*mut T, Option<RelocateToken>) {
        let full_sz = mem::size_of::<T>() + mem::size_of::<NkAtom>();
        let ret = (self.free.add(full_sz) >= self.offset(self.sz))
                  .then(|| self.make_room(full_sz));

        let cur = self.free as *mut NkAtom;
        let last = self.last;
        self.last = cur;

        self.free = (cur as *mut u8).add(full_sz);
        self.used += full_sz;
        self.num_atoms += 1;
        self.num_allocs += 1;

        (*cur).next = ptr::null_mut();
        (*cur).sz = mem::size_of::<T>() as NkSz;
        (*cur).set_color(Color::Black);
        (*cur).meta.set_typ(T::type_of() as u8);

        (*last).next = cur;

        let p = (cur as *mut u8).add(mem::size_of::<NkAtom>()) as *mut T;
        (p, ret)
    }

    #[inline]
    pub fn size_of<T: Fissile>() -> usize {
        mem::size_of::<T>() + mem::size_of::<NkAtom>()
    }

    #[inline]
    pub unsafe fn fit<T: Fissile>(&mut self, num: usize) -> RelocateToken {
        self.make_room(Nuke::size_of::<T>() * num)
    }

    #[inline]
    #[deprecated]
    pub unsafe fn fit_bytes(&mut self, num: usize) -> RelocateToken {
        self.make_room(num)
    }

    pub fn head(&mut self) -> *mut NkAtom {
        unsafe { (*self.fst()).next }
    }

    pub fn iter_mut(&mut self) -> NukeIterMut<'_> {
        NukeIterMut { item: self.head(),
                      _phantom: Default::default() }
    }

    pub fn iter(&self) -> NukeIter<'_> {
        let item = unsafe {
            (*(self.mem.as_ptr() as *const NkAtom)).next
        };
        NukeIter { item, _phantom: Default::default() }
    }

    pub fn reloc(&self) -> &PtrMap {
        &self.reloc
    }

    pub fn num_atoms(&self) -> usize {
        self.num_atoms
    }

    /// TODO: make `used`, `sz`, and `num_atoms` atomic.
    ///       Then create a begin_profile(t, sz) method that spawns
    ///       a thread which will save GCStats every t seconds until
    ///       it reaches sz samples. stop_profile() -> Vec<GCStats>
    ///       retrieves the stats.
    pub fn stats(&self) -> GCStats {
        GCStats {
            usage: self.used,
            size: self.sz,
            num_objects: self.num_atoms,
            total_allocs: self.num_allocs,
            total_frees: self.num_frees,
            #[cfg(not(target_arch = "wasm32"))]
            time: SystemTime::now().duration_since(self.start_time)
                                   .unwrap(),
        }
    }
}

struct RawDebugStr<'a>(&'a str);

impl fmt::Debug for RawDebugStr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

struct DebugHexBytes<'a>(&'a [u8]);

impl fmt::Debug for DebugHexBytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if f.alternate() {
            writeln!(f, "[")?;
            write!(f, "    ")?;
            for (i, c) in self.0.iter().enumerate() {
                write!(f, "{:02X}", c)?;
                if (i+1) % 30 == 0 && i+1 != self.0.len() {
                    writeln!(f)?;
                    write!(f, "    ")?;
                } else {
                    write!(f, " ")?;
                }
            }
            writeln!(f)?;
            write!(f, "]")?;
        } else {
            for c in self.0.iter() {
                write!(f, "{:02X}", c)?;
            }
        }
        Ok(())
    }
}

impl fmt::Debug for NkAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let fmted = self.lisp_to_string(&SYM_DB);
        f.debug_struct("NkAtom")
         .field("type", &self.type_of())
         .field("color", &self.color())
         .field("sz", &self.sz)
         .field("this", &(self as *const NkAtom))
         .field("next", &self.next)
         .field("obj", &RawDebugStr(&fmted))
         .field("raw", &DebugHexBytes(self.raw()))
         .finish()
    }
}

impl fmt::Debug for Nuke {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Nuke")
         .field("sz", &self.sz)
         .field("used", &self.used)
         .field("mem", &self.iter().collect::<Vec<_>>())
         .finish()
    }
}

pub struct NukeIterMut<'a> {
    item: *mut NkAtom,
    _phantom: PhantomData<&'a NkAtom>
}

impl<'a> Iterator for NukeIterMut<'a> {
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

pub struct NukeIter<'a> {
    item: *const NkAtom,
    _phantom: PhantomData<&'a NkAtom>
}

impl<'a> Iterator for NukeIter<'a> {
    type Item = &'a NkAtom;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item.is_null() { return None; }
        unsafe {
            let item = &*self.item;
            self.item = item.next;
            Some(item)
        }
    }
}


type NkSz = u16;

const META_COLOR_MASK: u8 = 0x03;
const META_TYPE_MASK: u8 = 0xfc;

pub struct AtomMeta(u8);

#[cfg(target_pointer_width = "32")]
#[repr(C, align(4))]
pub struct NkAtom {
    next: *mut NkAtom,
    sz: NkSz,
    meta: AtomMeta,
}

#[cfg(target_pointer_width = "64")]
#[repr(C, align(8))]
pub struct NkAtom {
    next: *mut NkAtom,
    sz: NkSz,
    meta: AtomMeta,
}

impl AtomMeta {
    #[inline]
    pub fn typ(&self) -> u8 {
        (self.0 & META_TYPE_MASK) >> 2
    }

    #[inline]
    pub fn color(&self) -> u8 {
        self.0 & META_COLOR_MASK
    }

    #[inline]
    pub fn set_color(&mut self, color: u8) {
        debug_assert!(color < 4, "Bitfield content out of range");
        self.0 = (self.0 & META_TYPE_MASK) | color;
    }

    #[inline]
    pub fn set_typ(&mut self, typ: u8) {
        debug_assert!(typ < 64, "Type number too large");
        self.0 = (self.0 & META_COLOR_MASK) | (typ << 2);
    }
}

#[derive(Debug)]
struct PtrPair {
    fst: *mut u8,
    snd: *mut u8,
}

impl PartialEq for PtrPair {
    fn eq(&self, other: &PtrPair) -> bool {
        other.fst == self.fst
    }
}

impl Eq for PtrPair {}

impl PartialOrd for PtrPair {
    fn partial_cmp(&self, other: &PtrPair) -> Option<Ordering> {
        self.fst.partial_cmp(&other.fst)
    }
}

impl Ord for PtrPair {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fst.cmp(&other.fst)
    }
}

#[derive(Debug)]
pub struct PtrMap(Vec<PtrPair>);

impl PtrMap {
    pub fn get<T>(&self, orig: *const T) -> *const T {
        let srch = PtrPair { fst: orig as *mut u8,
                             snd: ptr::null_mut::<u8>() };
        match self.0.binary_search(&srch) {
            Ok(idx) => self.0[idx].snd as *const T,
            Err(_) => orig
        }
    }

    pub fn len(&self) -> usize {
        self.0.len() as usize
    }

    pub fn push<A, B>(&mut self, from: *const A, to: *const B) {
        self.0.push(PtrPair { fst: from as *mut u8,
                              snd: to as *mut u8 })
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
