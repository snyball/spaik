//! The Nuclear Allocator

use crate::error::Error;
use crate::nkgc::{PV, Traceable, Arena, SymID, GCStats, Cons};
use crate::compile::Builtin;
use crate::fmt::{LispFmt, VisitSet, FmtWrap};
use crate::subrs::{IntoLisp, FromLisp};
use crate::sym_db::{SymDB, SYM_DB};
use core::slice;
use std::any::{TypeId, Any, type_name};
use std::mem::{self, size_of, align_of};
use std::ptr::{drop_in_place, self};
use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::fmt::{self, Display};
use core::fmt::Debug;
use std::sync::atomic::AtomicU32;
#[cfg(not(target_arch = "wasm32"))]
use std::time::SystemTime;
use fnv::FnvHashMap;
use std::sync::Mutex;
use std::collections::hash_map::Entry;
use std::alloc::{Layout, alloc, dealloc};
use std::sync::atomic;

macro_rules! with_atom {
    ($item:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match (*$item).type_of() {
                $(NkT::$t => {
                    let $item = fastcast::<$path>($item);
                    $fn
                }),+
            }
        }
    }
}

macro_rules! with_atom_mut {
    ($item:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match (*$item).type_of() {
                $(NkT::$t => {
                    let $item = fastcast_mut::<$path>($item);
                    $fn
                }),+
            }
        }
    }
}

macro_rules! with_atom_inst {
    ($item:ident, $what:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match (*$item).type_of() {
                $(NkT::$t => $what::$t({
                    let $item = fastcast_mut::<$path>($item);
                    $fn
                })),+
            }
        }
    }
}


/// Structs that can be stored inline in the GC `Arena` memory must implement
/// this trait.
///
/// # Safety
///
/// No. Not safe. Do not implement this trait directly.
///
/// Add your new internal heap-storage type to the `fissile_types! {...}`
/// list, or just use `Object`. This is essentially just a marker-type.
///
/// What makes it really gnarly to implement this trait yourself,
/// without adding it to `fissile_types! {...}` is that `type_of()` is used
/// as an index into `DESTRUCTORS` when deallocating unreachable GC
/// objects, and to figure out which pointers to follow during the GC
/// mark phase. This will obviously cause UB if the memory layout of your
/// type isn't what the destructor, or `trace`/`update_ptrs` expects
pub unsafe trait Fissile: LispFmt + Debug + Clone + Traceable + Any + 'static {
    fn type_of() -> NkT;
}

macro_rules! fissile_types {
    ($(($t:ident, $sym_type_of:expr, $path:path)),+) => {
        #[derive(Debug)]
        pub enum NkSum { $($t($path)),+ }

        #[repr(u8)]
        #[derive(Debug, PartialEq, Eq)]
        pub enum NkT { $($t),+ }

        #[derive(Debug)]
        pub enum NkMut { $($t(*mut $path)),+ }

        #[derive(Debug)]
        pub enum NkRef { $($t(* const $path)),+ }

        impl From<NkT> for SymID {
            fn from(src: NkT) -> SymID {
                match src { $(NkT::$t => $sym_type_of),+ }
            }
        }

        impl NkRef {
            pub fn type_of(&self) -> NkT {
                match self { $(Self::$t(..) => NkT::$t ),+ }
            }
        }

        impl NkMut {
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

        // TODO: When `if` inside const is stabilized you can make this a const fn,
        //       by calling a recursive const fn min()
        fn minimal_fissile_sz() -> NkSz {
            const LEN: usize = count_args!($($t),+);
            const SIZES: [usize; LEN] = [
                $(mem::size_of::<$path>()),+
            ];
            *SIZES.iter().min().unwrap() as NkSz
        }

        const DESTRUCTORS: [unsafe fn (*mut u8); count_args!($($t),+)] = [
            $(|x| { unsafe { drop_in_place(x as *mut $path) } }),+
        ];

        #[inline]
        pub fn update_ptr_atom(atom: *mut NkAtom, reloc: &PtrMap) {
            with_atom_mut!(atom, {(*atom).update_ptrs(reloc)},
                           $(($t,$path)),+)
        }

        #[inline]
        pub fn mark_atom(atom: *mut NkAtom, gray: &mut Vec<*mut NkAtom>) {
            with_atom_mut!(atom, {(*atom).trace(gray)}, $(($t,$path)),+);
            unsafe {
                (*atom).set_color(Color::Black)
            }
        }

        #[inline]
        pub fn to_fissile_mut<'a>(atom: *mut NkAtom) -> NkMut {
            with_atom_inst!(atom, NkMut, {atom}, $(($t,$path)),+)
        }

        #[inline]
        pub fn to_fissile_ref<'a>(atom: *const NkAtom) -> NkRef {
            let atom = atom as *mut NkAtom;
            with_atom_inst!(atom, NkRef, {atom}, $(($t,$path)),+)
        }

        #[inline]
        pub fn atom_fmt(p: *const NkAtom,
                        db: &dyn SymDB,
                        visited: &mut VisitSet,
                        f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if visited.get(&p).is_some() {
                write!(f, "(...)")
            } else {
                visited.insert(p);
                with_atom!(p, { (*p).lisp_fmt(db, visited, f) },
                           $(($t,$path)),+)
            }
        }

        #[inline]
        pub fn atom_to_str(p: *const NkAtom, db: &dyn SymDB) -> String {
            struct P(*const NkAtom);
            impl LispFmt for P {
                fn lisp_fmt(&self,
                            db: &dyn SymDB,
                            v: &mut VisitSet,
                            f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    atom_fmt(self.0, db, v, f)
                }
            }
            P(p).lisp_to_string(db)
        }

        $(unsafe impl Fissile for $path {
            fn type_of() -> NkT { NkT::$t }
        })+
    };
}

/// Marker-trait for data that can be stored inside a SPAIK `Object`, and
/// referred to from Rust using `Gc<T>`.
pub trait Userdata: LispFmt + Debug + Clone + Traceable + Any + 'static {}

pub trait CloneIterator: Iterator + Traceable {
    fn clone_box(&self) -> Box<dyn CloneIterator<Item = Self::Item>>;
}

impl<T> CloneIterator for T
where
    T: 'static + Iterator + Clone + Traceable,
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
        Self { root: self.root,
               it: self.it.clone_box() }
    }
}

impl IntoLisp for Iter {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put(self))
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
        self.it.trace(gray);
        self.root.trace(gray)
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        self.it.update_ptrs(reloc);
        self.root.update_ptrs(reloc)
    }
}

impl LispFmt for Iter {
    fn lisp_fmt(&self,
                db: &dyn SymDB,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(iter {})", FmtWrap { val: &self.root, db })
    }
}

impl Iterator for Iter {
    type Item = PV;

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next()
    }
}

/// Rust doesn't expose its vtables via any stable API, so we need to recreate
/// what we need for `Object` here.
#[derive(Clone)]
pub struct VTable {
    /// Result of `Any::type_name`
    type_name: &'static str,
    /// Get reference count
    get_rc: unsafe fn(*const u8) -> u32,
    /// `Traceable::trace`
    trace: unsafe fn(*const u8, gray: &mut Vec<*mut NkAtom>),
    /// `Traceable::update_ptrs`
    update_ptrs: unsafe fn(*mut u8, reloc: &PtrMap),
    /// `Drop::drop`
    drop: unsafe fn(*mut u8),
    /// `LispFmt::lisp_fmt`
    lisp_fmt: unsafe fn(*const u8, db: &dyn SymDB, visited: &mut VisitSet, f: &mut fmt::Formatter<'_>) -> fmt::Result,
    /// `Debug::fmt`
    fmt: unsafe fn(*const u8, f: &mut fmt::Formatter<'_>) -> fmt::Result,
}

impl Debug for VTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VTable")
         .field("type_name", &self.type_name)
         .field("get_rc", &self.get_rc)
         .field("trace", &(self.trace as *mut u8))
         .field("update_ptrs", &(self.update_ptrs as *mut u8))
         .field("drop", &self.drop)
         .field("lisp_fmt", &(self.lisp_fmt as *mut u8))
         .field("fmt", &(self.fmt as *mut u8))
         .finish()
    }
}

unsafe impl Send for VTable {}

/// How SPAIK sees objects internally, for referring to objects outside of the
/// SPAIK internals (library user code) see `Gc<T>`.
#[derive(Clone)]
pub struct Object {
    type_id: TypeId,
    vt: &'static VTable,
    /// This indirection allows us to safely pass references to the underlying T
    /// to user code, without having to worry about updating the pointer when
    /// the GC compacts. Of course, this also sacrifices some of the utility of
    /// the compacting process.
    ///
    /// See RcMem<T> for the actual layout of this memory.
    mem: *mut u8,
}

/// Reference-counter for `Object` memory, see `RcMem`
#[derive(Default)]
pub struct GcRc(AtomicU32);

impl GcRc {
    pub fn inc(&mut self) {
        self.0.fetch_add(1, atomic::Ordering::SeqCst);
    }

    pub fn is_dropped(&mut self) -> bool {
        self.0.fetch_sub(1, atomic::Ordering::SeqCst) == 1
    }
}

/// A `T` with a reference-counter stored right after it, uses repr(C) for
/// consistent memory layout.
#[repr(C)]
pub struct RcMem<T> {
    /// `obj` *must* be the first item of this struct, the `Object`
    /// implementation relies on being able to coerce a `*mut RcMem<T>` into a
    /// `*mut T`.
    obj: T,
    rc: GcRc
}

impl Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Object {{ ")?;
        unsafe {
            (self.vt.fmt)(self.mem, f)?;
        }
        write!(f, " }}")?;
        Ok(())
    }
}

impl LispFmt for Object {
    fn lisp_fmt(&self, db: &dyn SymDB, visited: &mut VisitSet, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe {
            (self.vt.lisp_fmt)(self.mem, db, visited, f)
        }
    }
}

/// Simplify types `ta` and `tb`, so that they are as short as possible while
/// being both distinct from each other and complete.
/// Essentially (x::y::abc, x::b::rac) becomes (abc, rac) while
///             (x::y::abc, x::b::abc) becomes (y::abc, b::abc)
fn simplify_types<'a, 'b>(ta: &'a str, tb: &'b str) -> (&'a str, &'b str) {
    let it = ta.bytes().enumerate().rev().zip(
             tb.bytes().enumerate().rev());
    for ((ia, ca), (ib, cb)) in it {
        if ca != cb {
            return (&ta[ta[..ia].rfind(':').map(|i| i + 1).unwrap_or(0)..],
                    &tb[tb[..ib].rfind(':').map(|i| i + 1).unwrap_or(0)..])
        }
    }
    (ta, tb)
}

pub unsafe fn ud_layout<T: Userdata>() -> Layout {
    Layout::from_size_align(size_of::<RcMem<T>>(),
                            align_of::<RcMem<T>>())
        .unwrap_unchecked()
}

pub unsafe fn drop_ud<T: Userdata>(obj: *mut u8) {
    drop_in_place(obj as *mut T);
    dealloc(obj, ud_layout::<T>());
}

pub struct ObjPtrMut(pub *mut Object);

impl ObjPtrMut {
    pub unsafe fn rc(&self) -> u32 {
        ((*self.0).vt.get_rc)((*self.0).mem)
    }

    pub unsafe fn cast_mut<T: Userdata>(&self) -> Result<*mut T, Error> {
        if TypeId::of::<T>() != (*self.0).type_id {
            let expect_t = type_name::<T>();
            let actual_t = (*self.0).vt.type_name;
            let (expect_t, actual_t) = simplify_types(expect_t, actual_t);
            return Err(error!(STypeError,
                        expect: format!("(object {expect_t})"),
                        got: format!("(object {actual_t})"),)
                        .argn(0).op(Builtin::Nil.sym()))
        }
        Ok((*self.0).mem as *mut T)
    }

    pub unsafe fn cast<T: Userdata>(&self) -> Result<*const T, Error> {
        Ok((*self.0).cast_mut()? as *const T)
    }

    pub unsafe fn fastcast_mut<T: Userdata>(&mut self) -> *mut T {
        (*self.0).mem as *mut T
    }

    pub unsafe fn fastcast<T: Userdata>(&self) -> *const T {
        (*self.0).mem as *const T
    }
}

impl Display for ObjPtrMut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { ((*self.0).vt.fmt)((*self.0).mem, f) }
    }
}

pub struct ObjPtr(pub *const Object);

impl ObjPtr {
    pub unsafe fn rc(&self) -> u32 {
        ((*self.0).vt.get_rc)((*self.0).mem)
    }

    pub unsafe fn cast<T: Userdata>(&self) -> Result<*const T, Error> {
        if TypeId::of::<T>() != (*self.0).type_id {
            let expect_t = type_name::<T>();
            let actual_t = (*self.0).vt.type_name;
            let (expect_t, actual_t) = simplify_types(expect_t, actual_t);
            return Err(error!(STypeError,
                        expect: format!("(object {expect_t})"),
                        got: format!("(object {actual_t})"),)
                        .argn(0).op(Builtin::Nil.sym()))
        }
        Ok((*self.0).mem as *mut T)
    }

    pub unsafe fn fastcast<T: Userdata>(&self) -> *const T {
        (*self.0).mem as *const T
    }
}

impl Display for ObjPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { ((*self.0).vt.fmt)((*self.0).mem, f) }
    }
}

impl Object {
    pub fn new<T: Userdata>(obj: T) -> Object {
        lazy_static! {
            static ref VTABLES: Mutex<FnvHashMap<TypeId, &'static VTable>> =
                Mutex::new(FnvHashMap::default());
        }
        macro_rules! delegate {($name:ident($($arg:ident),*)) => {
            |this, $($arg),*| unsafe { (*(this as *mut T)).$name($($arg),*) }
        }}
        let layout = unsafe { ud_layout::<T>() };
        let vtable = match VTABLES.lock().unwrap().entry(TypeId::of::<T>()) {
            Entry::Occupied(vp) => *vp.get(),
            Entry::Vacant(entry) => {
                entry.insert(Box::leak(Box::new(VTable {
                    type_name: type_name::<T>(),
                    drop: |obj| unsafe {
                        let rc_mem = obj as *mut RcMem<T>;
                        if (*rc_mem).rc.is_dropped() {
                            drop_ud::<T>(obj);
                        }
                    },
                    get_rc: |obj| unsafe {
                        let rc_mem = obj as *mut RcMem<T>;
                        (*rc_mem).rc.0.load(atomic::Ordering::SeqCst)
                    },
                    trace: delegate! { trace(gray) },
                    update_ptrs: delegate! { update_ptrs(reloc) },
                    lisp_fmt: delegate! { lisp_fmt(db, visited, f) },
                    fmt: delegate! { fmt(f) },
                })))
            },
        };
        let mem = unsafe {
            let p = alloc(layout) as *mut T;
            ptr::write(p, obj);
            (*(p as *mut RcMem<T>)).rc = GcRc(1.into());
            p as *mut u8
        };
        Object {
            type_id: TypeId::of::<T>(),
            vt: vtable,
            mem
        }
    }

    pub fn rc(&self) -> u32 {
        unsafe { (self.vt.get_rc)(self.mem) }
    }

    pub fn cast_mut<T: Userdata>(&self) -> Result<*mut T, Error> {
        if TypeId::of::<T>() != self.type_id {
            let expect_t = type_name::<T>();
            let actual_t = self.vt.type_name;
            let (expect_t, actual_t) = simplify_types(expect_t, actual_t);
            return Err(error!(STypeError,
                        expect: format!("(object {expect_t})"),
                        got: format!("(object {actual_t})"),)
                        .argn(0).op(Builtin::Nil.sym()))
        }
        Ok(self.mem as *mut T)
    }

    pub fn cast<T: Userdata>(&self) -> Result<*const T, Error> {
        Ok(self.cast_mut()? as *const T)
    }

    pub unsafe fn fastcast_mut<T: Userdata>(&mut self) -> *mut T {
        self.mem as *mut T
    }

    pub unsafe fn fastcast<T: Userdata>(&self) -> *const T {
        self.mem as *const T
    }
}

impl Traceable for Object {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        unsafe {
            (self.vt.trace)(self.mem, gray);
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        unsafe {
            (self.vt.update_ptrs)(self.mem, reloc);
        }
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        unsafe {
            (self.vt.drop)(self.mem);
        }
    }
}

/// Thread-safe reference-counted smart-pointer. Cheap to clone. Used to refer
/// to `Userdata` stored on the SPAIK heap.
///
/// Gc<T> survives your VM getting dropped, so you can create a reference to
/// something that you intend for a VM to modify, and then keep the reference
/// after the VM is no longer necessary.
///
/// Remember that you have to actually run the VM occasionally for the GC to
/// eventually drop these references.
///
/// In order for Gc<T> to be `Send`/`Sync` it requires that `T` is too, it
/// doesn't do any synchronization magic on `T` itself.
pub struct Gc<T> where T: Userdata {
    this: *mut RcMem<T>,
}

unsafe impl<T: ?Sized + Sync + Send + Userdata> Send for Gc<T> {}
unsafe impl<T: ?Sized + Sync + Send + Userdata> Sync for Gc<T> {}

impl<T: Userdata> Gc<T> {
    /// # Why does this take an `Fn` instead of an `FnMut`?
    ///
    /// Because you should not be able to call `with` on a potentially aliased
    /// Gc<T> inside `with` recursively, then you could have multiple `&mut`
    /// references to the same data and that is UB in Rust.
    ///
    /// You should use `with` only for simple setter/getter operations on the
    /// underlying `T` and nothing else.
    #[inline]
    pub fn with<R>(&mut self, f: impl Fn(&mut T) -> R) -> R {
        f(unsafe { &mut *(self.this as *mut T) })
    }
}

impl<T> Clone for Gc<T> where T: Userdata {
    fn clone(&self) -> Self {
        unsafe { (*self.this).rc.inc() }
        Self { this: self.this }
    }
}

impl<T> Debug for Gc<T> where T: Userdata {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe { (*self.this).obj.fmt(f) }
    }
}

impl<T> fmt::Display for Gc<T> where T: fmt::Display + Userdata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", unsafe { &(*self.this).obj })
    }
}

/// # Safety
/// This is safe for Userdata, because of the additional indirection.
/// They are not stored inline by the GC, the GC only has a pointer to it. This
/// means that unlike other PV ref-types the pointer does not move, and it is
/// therefore sufficient to keep an SPV reference-counter to avoid
/// dangling-pointer references.
impl<T> FromLisp<Gc<T>> for PV where T: Userdata {
    fn from_lisp(self, _mem: &mut Arena) -> Result<Gc<T>, Error> {
        with_ref!(self, Struct(s) => {
            let this = ((*s).cast_mut()? as *mut T) as *mut RcMem<T>;
            unsafe { (*this).rc.inc() }
            Ok(Gc { this })
        })
    }
}

impl<T: Userdata> Drop for Gc<T> {
    fn drop(&mut self) {
        unsafe {
            if (*self.this).rc.is_dropped() {
                drop_ud::<T>(self.this as *mut u8);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Continuation {
    stack: Option<Vec<PV>>,
    pub frame: usize,
    pub dip: usize,
}

impl Continuation {
    pub fn new(stack: Vec<PV>, frame: usize, dip: usize) -> Continuation {
        Continuation { stack: Some(stack), frame, dip }
    }

    pub fn take_stack(&mut self) -> Result<Vec<PV>, Error> {
        self.stack.take()
                  .ok_or_else(|| error!(Unsupported, op: "recursive-continuation"))
    }

    pub fn put_stack(&mut self, stak: Vec<PV>) {
        self.stack = Some(stak)
    }
}

impl Traceable for Continuation {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        if let Some(ref stack) = self.stack {
            for pv in stack.iter() {
                pv.trace(gray)
            }
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        if let Some(ref mut stack) = self.stack {
            for pv in stack.iter_mut() {
                pv.update_ptrs(reloc)
            }
        }
    }
}

impl LispFmt for Continuation {
    fn lisp_fmt(&self,
                db: &dyn SymDB,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref stack) = self.stack {
            writeln!(f, "stack:")?;
            if stack.is_empty() {
                writeln!(f, "    (empty)")?;
            }
            for (idx, val) in stack.iter().enumerate().rev() {
                let (idx, frame) = (idx as i64, self.frame as i64);
                write!(f, "{}", if idx == frame { " -> " } else { "    " })?;
                write!(f, "{}: ", idx - frame)?;
                val.lisp_fmt(db, visited, f)?;
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Intr {
    pub op: Builtin,
    pub arg: PV,
}

impl LispFmt for Intr {
    fn lisp_fmt(&self,
                db: &dyn SymDB,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", db.name(self.op.sym()))?;
        self.arg.lisp_fmt(db, visited, f)
    }
}

impl Traceable for Intr {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        self.arg.trace(gray)
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        self.arg.update_ptrs(reloc)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Void;

impl Traceable for Void {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {}

    fn update_ptrs(&mut self, reloc: &PtrMap) {}
}

impl LispFmt for Void {
    fn lisp_fmt(&self,
                db: &dyn SymDB,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "void")
    }
}

fissile_types! {
    (Void, Builtin::Void.sym(), Void),
    (Cons, Builtin::Cons.sym(), crate::nkgc::Cons),
    (Intr, Builtin::Intr.sym(), crate::nuke::Intr),
    (Lambda, Builtin::Lambda.sym(), crate::nkgc::Lambda),
    (VLambda, Builtin::Lambda.sym(), crate::nkgc::VLambda),
    (String, Builtin::String.sym(), std::string::String),
    (PV, Builtin::Ref.sym(), crate::nkgc::PV),
    (Vector, Builtin::Vector.sym(), Vec<PV>),
    (Vec4, Builtin::Vec4.sym(), glam::Vec4),
    (Mat2, Builtin::Mat2.sym(), glam::Mat2),
    (Mat3, Builtin::Mat3.sym(), glam::Mat3),
    (Mat4, Builtin::Mat4.sym(), glam::Mat4),
    (Stream, Builtin::Stream.sym(), crate::nkgc::Stream),
    (Struct, Builtin::Struct.sym(), crate::nuke::Object),
    (Iter, Builtin::Struct.sym(), crate::nuke::Iter),
    (Continuation, Builtin::Continuation.sym(), crate::nuke::Continuation),
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

macro_rules! trivial_trace {
    ($($t:ty),*) => {$(impl Traceable for $t {
        fn trace(&self, _gray: &mut Vec<*mut NkAtom>) {}
        fn update_ptrs(&mut self, _reloc: &PtrMap) {}
    })*};
}

trivial_trace!(glam::Vec2, glam::Vec3, glam::Vec4,
               glam::Mat2, glam::Mat3, glam::Mat4,
               glam::Quat);

impl NkAtom {
    #[inline]
    pub fn make_ref<T: Fissile>(p: *mut T) -> PV {
        PV::Ref(NkAtom::make_raw_ref(p))
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn make_raw_ref<T: Fissile>(p: *mut T) -> *mut NkAtom {
        const DELTA: isize = -(mem::size_of::<NkAtom>() as isize);
        unsafe {
            (p as *mut u8).offset(DELTA) as *mut NkAtom
        }
    }

    pub fn raw(&self) -> &[u8] {
        const DELTA: isize = mem::size_of::<NkAtom>() as isize;
        unsafe {
            let p = (self as *const NkAtom as *const u8).offset(DELTA);
            slice::from_raw_parts(p, self.sz as usize)
        }
    }

    #[inline]
    pub fn color(&self) -> Color {
        unsafe { mem::transmute(self.meta.color()) }
    }

    #[inline]
    pub fn set_color(&mut self, color: Color) {
        unsafe { self.meta.set_color(mem::transmute(color)) }
    }

    #[inline]
    pub fn init(&mut self, typ: NkT) {
        unsafe { self.meta.init(mem::transmute(Color::Black),
                                mem::transmute(typ)) }
    }

    #[inline]
    pub fn type_of(&self) -> NkT {
        unsafe { mem::transmute(self.meta.typ()) }
    }

    pub fn full_size(&self) -> usize {
        mem::size_of::<NkAtom>() + self.sz as usize
    }
}

#[inline]
pub unsafe fn fastcast<T>(atom: *const NkAtom) -> *const T {
    const DELTA: isize = mem::size_of::<NkAtom>() as isize;
    (atom as *const u8).offset(DELTA) as *mut T
}

#[inline]
pub unsafe fn fastcast_mut<T>(atom: *mut NkAtom) -> *mut T {
    const DELTA: isize = mem::size_of::<NkAtom>() as isize;
    (atom as *mut u8).offset(DELTA) as *mut T
}

#[inline]
pub fn atom_kind(atom: *const NkAtom) -> NkT {
    unsafe { mem::transmute((*atom).meta.typ()) }
}

#[inline]
pub fn cast_mut<T: Fissile>(atom: *mut NkAtom) -> Option<*mut T> {
    unsafe {
        let ty = T::type_of();
        let got = mem::transmute((*atom).meta.typ());
        (ty == got).then(|| fastcast_mut::<T>(atom))
    }
}

#[inline]
pub fn cast<T: Fissile>(atom: *const NkAtom) -> Option<*const T> {
    cast_mut(atom as *mut NkAtom).map(|p| p as *const T)
}

#[inline]
pub unsafe fn destroy_atom(atom: *mut NkAtom) {
    DESTRUCTORS[(*atom).meta.typ() as usize](fastcast_mut::<u8>(atom));
}

pub fn clone_atom(atom: *const NkAtom, mem: &mut Arena) -> *mut NkAtom {
    macro_rules! clone {
        ($x:expr) => {{
            let p = mem.alloc();
            unsafe { ptr::write(p, (*$x).clone()) }
            NkAtom::make_raw_ref(p)
        }};
    }
    match to_fissile_ref(atom) {
        NkRef::Void(v) => clone!(v),
        NkRef::Cons(cns) => {
            let p = mem.alloc::<Cons>();
            unsafe {
                (*p).car = (*cns).car.deep_clone(mem);
                (*p).cdr = (*cns).cdr.deep_clone(mem);
            }
            NkAtom::make_raw_ref(p)
        },
        NkRef::Intr(intr) => {
            let p = mem.alloc::<Intr>();
            NkAtom::make_raw_ref(unsafe {
                ptr::write(p, Intr {
                    op: (*intr).op,
                    arg: (*intr).arg.deep_clone(mem),
                }); p
            })
        }
        NkRef::Lambda(_l) => todo!(),
        NkRef::VLambda(_l) => todo!(),
        NkRef::String(s) => clone!(s),
        NkRef::PV(_p) => todo!(),
        NkRef::Vector(xs) => unsafe {
            let nxs = (*xs).iter().map(|p| p.deep_clone(mem)).collect::<Vec<_>>();
            let p = mem.alloc();
            ptr::write(p, nxs);
            NkAtom::make_raw_ref(p)
        },
        NkRef::Vec4(v4) => clone!(v4),
        NkRef::Mat2(m2) => clone!(m2),
        NkRef::Mat3(m3) => clone!(m3),
        NkRef::Mat4(m4) => clone!(m4),
        NkRef::Stream(s) => clone!(s),
        NkRef::Struct(s) => clone!(s),
        NkRef::Iter(i) => clone!(i),
        NkRef::Continuation(_c) => todo!(),
        NkRef::Subroutine(s) => clone!(s),
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
    sz: usize,
    reloc: PtrMap,
    last: *mut NkAtom,
    mem: Vec<u8>,
    #[cfg(not(target_arch = "wasm32"))]
    start_time: SystemTime,
}

/// Modern computers really don't like it if you put a pointer in a memory
/// address that is not a multiple of the word size. In other words, the CPU
/// expects that ptr % sizeof(ptr) == 0, where sizeof(ptr) will be 4, and 8
/// for 32 and 64 bit architectures respectively. Other types (mostly things
/// related to SIMD (AFAIK)) may even require 16 bytes.
///
/// This function is an optimized method of computing the next valid memory
/// address starting at `p`, where a storage class of alignment `a` can be
/// placed (Note that T is arbtrary and is not used in the calculation, see
/// Layout::* for getting the alignment for a type.)
fn align<T>(p: *mut T, a: isize) -> *mut T {
    (((p as isize) + a - 1) & !(a - 1)) as *mut T
}

/// Equivalent to memcpy from ANSI C, void* and all. In almost all cases this is
/// not what you want, but in the dark corners of the computing stack, where the
/// untyped pointers play, and the light of the type system is all but
/// extinguished. In there, you can count on memcpy to just copy, byte-sized,
/// and do nothing else.
#[inline(always)]
pub unsafe fn memcpy<R, W>(dst: *mut W, src: *const R, sz: usize) {
    ptr::copy_nonoverlapping(src as *const u8, dst as *mut u8, sz);
}

/// Copy into `dst`, from `src`. The buffers may overlap. See `memcpy` for
/// copying memory regions that do not overlap.
#[allow(dead_code)]
#[inline(always)]
pub unsafe fn memmove<R, W>(dst: *mut W, src: *const R, sz: usize) {
    ptr::copy(src as *const u8, dst as *mut u8, sz);
}

#[cfg(target_pointer_width = "32")]
const ALIGNMENT: isize = 4;

// FIXME: It's not fair to make *all* types 16-byte aligned just because `Vec4` is
#[cfg(target_pointer_width = "64")]
const ALIGNMENT: isize = 8;

#[must_use = "Relocation must be confirmed"]
pub struct RelocateToken;

impl Nuke {
    pub fn new(sz: usize) -> Nuke {
        assert!(sz >= 128, "Nuke too small");

        let mut nk = Nuke {
            free: ptr::null_mut(),
            grow_num: sz,
            used: 0,
            num_frees: 0,
            num_allocs: 0,
            num_atoms: 0,
            sz,
            reloc: PtrMap(Vec::new()),
            last: ptr::null_mut(),
            mem: Vec::with_capacity(sz),
            #[cfg(not(target_arch = "wasm32"))]
            start_time: SystemTime::now(),
        };

        unsafe { nk.mem.set_len(sz) }
        nk.last = nk.fst_mut();
        nk.free = nk.offset(mem::size_of::<NkAtom>());
        nk.used = mem::size_of::<NkAtom>();
        unsafe {
            (*nk.fst_mut()).init(NkT::Void);
            (*nk.fst_mut()).next = ptr::null_mut();
            (*nk.fst_mut()).sz = 0;
        }
        nk.num_atoms = 1;

        nk
    }

    pub unsafe fn compact(&mut self) -> RelocateToken {
        let mut node = self.fst_mut();
        let mut npos;
        let mut start = node as *mut u8;

        loop {
            let next_node = (*node).next;
            npos = start as *mut NkAtom;
            let sz = mem::size_of::<NkAtom>() + (*node).sz as usize;
            if npos != node {
                self.reloc.push(node, npos);
                memmove(npos, node, sz); // memcpy should work, but miri no likey
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

        RelocateToken
    }

    pub unsafe fn destroy_the_world(&mut self) {
        for atom in self.iter_mut() {
            unsafe {
                // println!("{:?} {:?}", (*atom).type_of(), (*atom).color());
                // println!("{:?}", atom_kind(atom));
                // println!("i-i-i-i-i want to: {}", atom_to_str(atom, &SYM_DB));
                if let Some(obj) = cast::<Object>(atom) {
                    println!("{}", ObjPtr(obj))
                }
                destroy_atom(atom);
            }
        }
        self.last = self.fst_mut();
        self.free = self.offset(mem::size_of::<NkAtom>());
        self.used = mem::size_of::<NkAtom>();
        (*self.fst_mut()).next = ptr::null_mut();
        self.num_atoms = 1;
    }

    pub unsafe fn sweep_compact(&mut self) -> RelocateToken {
        let mut node = self.fst_mut();
        let mut npos;
        let mut start = node as *mut u8;

        loop {
            let next_node = {
                let mut num_frees = 0;
                let mut n = (*node).next;
                while !n.is_null() {
                    if (*n).color() == Color::White {
                        destroy_atom(n);
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
                memmove(npos, node, sz); // memcpy should work, but miri no likey
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
        (*self.fst_mut()).set_color(Color::Black);
        self.free = start;

        RelocateToken
    }

    pub unsafe fn grow(&mut self, fit: usize) -> RelocateToken {
        let new_sz = (self.sz << 1).max(self.sz + fit);
        self.sz = new_sz;

        let mut used = 0;
        let mut num_atoms = 0;

        let mut new_vec: Vec<u8> = Vec::with_capacity(new_sz);
        #[allow(clippy::uninit_vec)]
        new_vec.set_len(new_sz);
        let mut mem = align(new_vec.as_mut_ptr(),
                            mem::align_of::<NkAtom>() as isize);
        let mut new_node = ptr::null_mut();
        let mut node = self.fst_mut();
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

        RelocateToken
    }

    pub unsafe fn make_room(&mut self, fit: usize) -> RelocateToken {
        if self.used + fit > self.sz {
            self.grow(fit)
        } else {
            self.compact()
        }
    }

    pub fn confirm_relocation(&mut self, t: RelocateToken) {
        #[allow(clippy::drop_non_drop)] drop(t);
        self.reloc.0.clear();
    }

    pub fn fst_mut(&mut self) -> *mut NkAtom {
        align(self.mem.as_mut_ptr() as *mut NkAtom,
              mem::align_of::<NkAtom>() as isize)
    }

    pub fn fst(&self) -> *const NkAtom {
        align(self.mem.as_ptr() as *mut NkAtom,
              mem::align_of::<NkAtom>() as isize)
    }

    pub fn offset<T>(&mut self, n: usize) -> *mut T {
        unsafe {
            self.mem.as_mut_ptr().add(n) as *mut T
        }
    }

    pub unsafe fn alloc<T: Fissile>(&mut self) -> (*mut T, Option<RelocateToken>) {
        let cur = align(self.free as *mut NkAtom, ALIGNMENT);
        let p = (cur as *mut u8).add(mem::size_of::<NkAtom>()) as *mut T;
        let pa = align(p, align_of::<T>() as isize);
        let full_sz = mem::size_of::<T>()
                    + mem::size_of::<NkAtom>()
                    + ((pa as *const u8 as usize) - (p as *const u8 as usize));
        let ret = (self.free.add(full_sz) >= self.offset(self.sz))
                  .then(|| self.make_room(full_sz));

        let last = self.last;
        self.last = cur;

        self.free = (cur as *mut u8).add(full_sz);
        self.used += full_sz;
        self.num_atoms += 1;
        self.num_allocs += 1;

        (*cur).next = ptr::null_mut();
        (*cur).sz = mem::size_of::<T>() as NkSz;
        (*cur).init(T::type_of());

        (*last).next = cur;

        (pa, ret)
    }

    #[inline]
    pub fn size_of<T: Fissile>() -> usize {
        mem::size_of::<T>() + mem::size_of::<NkAtom>()
    }

    pub fn will_overflow(&mut self, sz: usize) -> bool {
        self.free as usize + sz >= self.offset::<u8>(self.sz) as usize
    }

    #[inline]
    pub unsafe fn fit<T: Fissile>(&mut self, num: usize) -> RelocateToken {
        let full_sz = Nuke::size_of::<T>() * num;
        if self.will_overflow(full_sz) {
            self.make_room(Nuke::size_of::<T>() * num)
        } else {
            RelocateToken
        }
    }

    pub fn head_mut(&mut self) -> *mut NkAtom {
        unsafe { (*self.fst_mut()).next }
    }

    pub fn head(&self) -> *const NkAtom {
        unsafe { (*self.fst()).next }
    }

    pub fn iter_mut(&mut self) -> NukeIterMut {
        NukeIterMut { item: self.head_mut() }
    }

    pub fn iter(&self) -> NukeIter {
        NukeIter { item: self.head() }
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
        // let fmted = self.lisp_to_string(&SYM_DB);
        f.debug_struct("NkAtom")
         .field("type", &self.type_of())
         .field("color", &self.color())
         .field("sz", &self.sz)
         .field("this", &(self as *const NkAtom))
         .field("next", &self.next)
         // .field("obj", &RawDebugStr(&fmted))
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

pub struct NukeIterMut {
    item: *mut NkAtom,
}

impl Iterator for NukeIterMut {
    type Item = *mut NkAtom;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item.is_null() { return None; }
        unsafe {
            let ret = self.item;
            self.item = (*self.item).next;
            Some(ret)
        }
    }
}

pub struct NukeIter {
    item: *const NkAtom,
}

impl Iterator for NukeIter {
    type Item = *const NkAtom;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item.is_null() { return None; }
        unsafe {
            let item = self.item;
            self.item = (*self.item).next;
            Some(item)
        }
    }
}


type NkSz = u16;

const META_COLOR_MASK: u8 = 0x03;
const META_TYPE_MASK: u8 = 0xfc;

pub struct AtomMeta(u8);

#[repr(C)]
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

    #[inline]
    pub fn init(&mut self, color: u8, typ: u8) {
        debug_assert!(color < 4, "Bitfield content out of range");
        debug_assert!(typ < 64, "Type number too large");
        self.0 = color | (typ << 2);
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
        self.0.len()
    }

    pub fn push<A, B>(&mut self, from: *const A, to: *const B) {
        self.0.push(PtrPair { fst: from as *mut u8,
                              snd: to as *mut u8 })
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simplify_types_test() {
        let ta = "crate::sum::shit::XYZ";
        let tb = "crate::sum::shit::XYZ";
        assert_eq!(simplify_types(ta, tb), (ta, tb));

        let ta = "crate::sum::shit::ABC";
        let tb = "crate::sum::shit::XYZ";
        assert_eq!(simplify_types(ta, tb), ("ABC", "XYZ"));

        let ta = "crate::hmm::shit::ABC";
        let tb = "crate::sum::shit::ABC";
        assert_eq!(simplify_types(ta, tb),
                   ("hmm::shit::ABC", "sum::shit::ABC"));

        let ta = "crate::hmm::sit::ABC";
        let tb = "crate::sum::shit::ABC";
        assert_eq!(simplify_types(ta, tb),
                   ("sit::ABC", "shit::ABC"));

        let ta = "crate::hmm::si::ABC";
        let tb = "crate::sum::shit::ABC";
        assert_eq!(simplify_types(ta, tb),
                   ("si::ABC", "shit::ABC"));
    }
}
