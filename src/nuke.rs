//! The Nuclear Allocator

use crate::error::{Error, OpName};
use crate::nkgc::{PV, Traceable, Arena, SymID, GCStats, Cons};
use crate::builtins::Builtin;
use crate::fmt::{LispFmt, VisitSet, FmtWrap};

use crate::subrs::{IntoLisp, FromLisp, self};
use core::slice;
use std::any::{TypeId, Any, type_name};
use std::io::{Write, Read};
use std::marker::PhantomData;
use std::mem::{self, size_of, align_of, MaybeUninit};
use std::ptr::{drop_in_place, self, null_mut};
use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::fmt::{self, Display};
use core::fmt::Debug;
use std::sync::atomic::AtomicU32;
#[cfg(not(target_arch = "wasm32"))]
use std::time::SystemTime;
use fnv::FnvHashMap;
#[cfg(feature = "freeze")]
use serde::{Serialize, Deserialize};
use std::sync::{Mutex, OnceLock};
use std::collections::hash_map::Entry;
use std::alloc::{Layout, alloc, dealloc, realloc, handle_alloc_error};
use std::sync::atomic;

macro_rules! with_atom {
    ($item:ident, $fn:block, $(($t:ident, $path:path)),+) => {
        unsafe {
            match atom_kind($item) {
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
            match atom_kind($item) {
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
            match atom_kind($item) {
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
pub unsafe trait Fissile: LispFmt + Debug + Traceable + Any + 'static {
    fn type_of() -> NkT;
}

macro_rules! fissile_types {
    ($(($t:ident, $sym_type_of:expr, $path:path)),+) => {
        #[repr(u8)]
        #[derive(Debug, PartialEq, Eq)]
        pub enum NkT { $($t),+ }

        #[derive(Debug)]
        pub enum NkMut { $($t(*mut $path)),+ }

        #[derive(Debug)]
        pub enum NkRef { $($t(* const $path)),+ }

        impl From<NkT> for SymID {
            fn from(src: NkT) -> SymID {
                let bt: Builtin = src.into();
                bt.sym_id()
            }
        }

        impl From<NkT> for Builtin {
            fn from(src: NkT) -> Builtin {
                match src { $(NkT::$t => $sym_type_of),+ }
            }
        }

        impl NkRef {
            #[allow(dead_code)]
            pub fn type_of(&self) -> NkT {
                match self { $(Self::$t(..) => NkT::$t ),+ }
            }
        }

        impl NkMut {
            #[allow(dead_code)]
            pub fn type_of(&self) -> NkT {
                match self { $(Self::$t(..) => NkT::$t ),+ }
            }
        }

        const DESTRUCTORS: [unsafe fn (*mut u8); count_args!($($t),+)] = [
            $(|x| { unsafe { drop_in_place(x as *mut $path) } }),+
        ];

        #[allow(dead_code)]
        const ALIGNMENTS: [usize; count_args!($($t),+)] = [
            $(align_of::<$path>()),+
        ];

        #[allow(dead_code)]
        const SIZES: [usize; count_args!($($t),+)] = [
            $(size_of::<$path>()),+
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
        pub fn to_fissile_mut(atom: *mut NkAtom) -> NkMut {
            with_atom_inst!(atom, NkMut, {atom}, $(($t,$path)),+)
        }

        #[allow(dead_code)]
        #[inline]
        pub fn assert_atom_inner_alignment(atom: *const NkAtom) {
            unsafe {
                match atom_kind(atom) {
                    $(NkT::$t => {
                        let item = fastcast::<$path>(atom);
                        assert_eq!(item as usize % align_of::<$path>(), 0);
                    }),+
                }
            }
        }

        #[inline]
        pub fn to_fissile_ref(atom: *const NkAtom) -> NkRef {
            let atom = atom as *mut NkAtom;
            with_atom_inst!(atom, NkRef, {atom}, $(($t,$path)),+)
        }

        pub fn atom_fmt(p: *const NkAtom,
                        visited: &mut VisitSet,
                        f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if visited.get(&p).is_some() {
                write!(f, "(...)")
            } else {
                visited.insert(p);
                with_atom!(p, { (*p).lisp_fmt(visited, f) },
                           $(($t,$path)),+)
            }
        }

        #[allow(dead_code)]
        pub fn atom_to_str(p: *const NkAtom) -> String {
            struct P(*const NkAtom);
            impl LispFmt for P {
                fn lisp_fmt(&self,
                            v: &mut VisitSet,
                            f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    atom_fmt(self.0, v, f)
                }
            }
            P(p).lisp_to_string()
        }

        $(unsafe impl Fissile for $path {
            fn type_of() -> NkT { NkT::$t }
        })+
    };
}

/// Marker-trait for data that can be stored inside a SPAIK `Object`, and
/// referred to from Rust using `Gc<T>`.
#[cfg(not(feature = "freeze"))]
pub trait Userdata: Debug + Any + 'static
{}
#[cfg(feature = "freeze")]
pub trait Userdata: Debug + Any +
    Serialize + serde::de::DeserializeOwned + 'static
{}

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
        Ok(mem.put_pv(self))
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
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(iter {})", FmtWrap { val: &self.root })
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
#[derive(Clone, PartialEq, Eq)]
pub struct VTable {
    /// Result of `Any::type_name`
    pub type_name: &'static str,
    pub type_id: TypeId,
    /// Get reference count
    get_rc: unsafe fn(*mut u8) -> Option<*mut GcRc>,
    /// `Drop::drop`
    drop: unsafe fn(*mut u8),
    /// `Debug::fmt`
    fmt: unsafe fn(*const u8, f: &mut fmt::Formatter<'_>) -> fmt::Result,
    /// `core::clone::Clone`
    clone: Option<unsafe fn(*const u8) -> Object>,
    /// Serialize the object
    #[allow(dead_code)]
    freeze: unsafe fn(*const u8, into: &mut dyn Write) -> usize,
}

pub struct OptVTable<T: Userdata> {
    /// `core::clone::Clone`
    clone: Option<unsafe fn(*const u8) -> Object>,
    _ph: std::marker::PhantomData<T>,
}

pub trait GetOptVTable<T: Userdata> {
    fn vtable() -> OptVTable<T>;
}

impl<T> GetOptVTable<T> for T where T: Userdata {
    fn vtable() -> OptVTable<T> {
        OptVTable::default()
    }
}

impl<T: Userdata> Default for OptVTable<T> {
    fn default() -> Self {
        Self { clone: Default::default(), _ph: Default::default() }
    }
}

impl<T: Userdata> OptVTable<T> {
}

pub trait CanClone<T: Sized + Userdata + Clone> {
    fn can_clone(self) -> Self;
}

impl<T> CanClone<T> for OptVTable<T> where T: Sized + Userdata + Clone {
    fn can_clone(mut self) -> Self {
        self.clone = Some(|mem: *const u8| unsafe {
            let obj = mem as *mut T;
            Object::new((*obj).clone())
        });
        self
    }
}

impl Debug for VTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VTable")
         .field("type_name", &self.type_name)
         .field("get_rc", &self.get_rc)
         .field("drop", &self.drop)
         .field("fmt", &(self.fmt as *mut u8))
         .finish()
    }
}

unsafe impl Send for VTable {}

/// How SPAIK sees objects internally, for referring to objects outside of the
/// SPAIK internals (library user code) see `Gc<T>`.
pub struct Object {
    pub(crate) type_id: TypeId,
    pub(crate) vt: &'static VTable,
    /// This indirection allows us to safely pass references to the underlying T
    /// to user code, without having to worry about updating the pointer when
    /// the GC compacts. Of course, this also sacrifices some of the utility of
    /// the compacting process.
    ///
    /// See RcMem<T> for the actual layout of this memory.
    pub(crate) mem: *mut u8,
}

pub struct Locked;

impl Clone for Object {
    fn clone(&self) -> Self {
        unsafe { (self.vt.get_rc)(self.mem).map(|rc| (*rc).inc()) };
        Self { type_id: self.type_id,
               vt: self.vt,
               mem: self.mem }
    }
}

/// Reference-counter for `Object` memory, see `RcMem`
#[derive(Default)]
pub struct GcRc(AtomicU32);

impl GcRc {
    pub const fn new(init: AtomicU32) -> GcRc {
        GcRc(init)
    }

    pub fn inc(&self) {
        self.0.fetch_add(1, atomic::Ordering::SeqCst);
    }

    pub fn is_dropped(&self) -> bool {
        self.0.fetch_sub(1, atomic::Ordering::SeqCst) == 1
    }

    pub fn is_owned(&self) -> bool {
        self.0.load(atomic::Ordering::SeqCst) == 1
    }

    pub fn num_refs(&self) -> u32 {
        self.0.load(atomic::Ordering::SeqCst)
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
    fn lisp_fmt(&self, _visited: &mut VisitSet, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe {
            (self.vt.fmt)(self.mem, f)
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

pub unsafe fn ud_layout<T>() -> Layout {
    Layout::from_size_align(size_of::<RcMem<T>>(),
                            align_of::<RcMem<T>>())
        .unwrap_unchecked()
}

pub unsafe fn drop_ud<T>(obj: *mut u8) {
    drop_in_place(obj as *mut T);
    dealloc(obj, ud_layout::<T>());
}

pub struct ObjPtrMut(pub *mut Object);

impl ObjPtrMut {
    pub unsafe fn cast_mut<T: Userdata>(&self) -> Result<*mut T, Error> {
        if TypeId::of::<T>() != (*self.0).type_id {
            let expect_t = type_name::<T>();
            let actual_t = (*self.0).vt.type_name;
            let (expect_t, actual_t) = simplify_types(expect_t, actual_t);
            return Err(error!(STypeError,
                        expect: format!("(object {expect_t})"),
                        got: format!("(object {actual_t})"),)
                        .argn(0).bop(Builtin::Nil))
        }
        Ok((*self.0).mem as *mut T)
    }
}

impl Display for ObjPtrMut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { ((*self.0).vt.fmt)((*self.0).mem, f) }
    }
}

pub struct ObjPtr(pub *const Object);

impl ObjPtr {
    pub unsafe fn cast<T: Userdata>(&self) -> Result<*const T, Error> {
        if TypeId::of::<T>() != (*self.0).type_id {
            let expect_t = type_name::<T>();
            let actual_t = (*self.0).vt.type_name;
            let (expect_t, actual_t) = simplify_types(expect_t, actual_t);
            return Err(error!(STypeError,
                        expect: format!("(object {expect_t})"),
                        got: format!("(object {actual_t})"),)
                        .argn(0).bop(Builtin::Nil))
        }
        Ok((*self.0).mem as *mut T)
    }
}

impl Display for ObjPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { ((*self.0).vt.fmt)((*self.0).mem, f) }
    }
}

pub type ThawFn = fn(from: &mut dyn Read) -> Result<Object, Error>;

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct TypePath(&'static str);

#[allow(dead_code)]
impl TypePath {
    pub fn of<T: ?Sized>() -> Self {
        TypePath(type_name::<T>())
    }
}

static VTABLES: OnceLock<Mutex<FnvHashMap<TypeId, &'static VTable>>> = OnceLock::new();
static THAW_FNS: OnceLock<Mutex<FnvHashMap<TypePath, ThawFn>>> = OnceLock::new();
#[cfg(all(not(miri), any(test, feature = "cleanup-vtables")))]
pub static NUM_VMS: Mutex<i32> = Mutex::new(0);

pub fn get_vtables() -> &'static Mutex<FnvHashMap<TypeId, &'static VTable>> {
    VTABLES.get_or_init(|| Mutex::new(FnvHashMap::default()))
}

#[allow(dead_code)]
pub fn get_thaw_fns() -> &'static Mutex<FnvHashMap<TypePath, ThawFn>> {
    THAW_FNS.get_or_init(|| Mutex::new(FnvHashMap::default()))
}

pub fn vm_begin() {
    #[cfg(all(not(miri), any(test, feature = "cleanup-vtables")))] {
        let mut num = NUM_VMS.lock().unwrap();
        *num = *num + 1;
    }
}

pub fn vm_end() {
    #[cfg(all(not(miri), any(test, feature = "cleanup-vtables")))] {
        let mut num_vms = NUM_VMS.lock().unwrap();
        *num_vms = *num_vms - 1;
        if *num_vms > 0 { return }
        log::info!("clearing vtables ...");
        let mut vts = get_vtables().lock().unwrap();
        for (_id, vt) in vts.drain() {
            unsafe { drop(Box::from_raw(vt as *const VTable as *mut VTable)) }
        }
        vts.shrink_to_fit();
        let mut thaw_fns = get_thaw_fns().lock().unwrap();
        thaw_fns.drain().for_each(drop);
        thaw_fns.shrink_to_fit();
    }
}

/// # Safety
///
/// The only safe place to run this function is before any VMs are constructed,
/// and after all VMs have been destroyed.
#[allow(dead_code)]
pub unsafe fn clear_vtables() {
    let mut vts = get_vtables().lock().unwrap();
    for (_id, vt) in vts.drain() {
        unsafe { drop(Box::from_raw(vt as *const VTable as *mut VTable)) }
    }
    vts.shrink_to_fit();
}

#[repr(C)]
pub struct Voided;

// static VT_VOID: &'static VTable = VTable {
//     type_name: "void",
//     get_rc: |obj| { 1 },
//     trace: todo!(),
//     update_ptrs: todo!(),
//     drop: todo!(),
//     lisp_fmt: todo!(),
//     fmt: todo!(),
//     call: todo!(),
//     freeze: todo!(),
// };

impl Object {
    pub fn register<T: Userdata + 'static>(opt: OptVTable<T>) -> &'static VTable {
        macro_rules! delegate {($name:ident($($arg:ident),*)) => {
            |this, $($arg),*| unsafe { (*(this as *mut T)).$name($($arg),*) }
        }}
        #[cfg(feature = "freeze")]
        let thaw_fns = THAW_FNS.get_or_init(|| Mutex::new(FnvHashMap::default()));
        #[cfg(feature = "freeze")]
        if let Entry::Vacant(e) = thaw_fns.lock().unwrap().entry(TypePath::of::<T>()) {
            e.insert(|from| {
                use bincode::Options;
                let opts = bincode::DefaultOptions::new();
                let obj: T = opts.deserialize_from(from).unwrap();
                Ok(Object::new(obj))
            });
        }
        let vtables = get_vtables();
        match vtables.lock().unwrap().entry(TypeId::of::<T>()) {
            Entry::Occupied(vp) => vp.get(),
            Entry::Vacant(entry) => {
                entry.insert(Box::leak(Box::new(VTable {
                    type_name: type_name::<T>(),
                    type_id: TypeId::of::<T>(),
                    drop: |obj| unsafe {
                        let rc_mem = obj as *mut RcMem<T>;
                        if (*rc_mem).rc.is_dropped() {
                            drop_ud::<T>(obj);
                        }
                    },
                    get_rc: |obj| unsafe {
                        let rc_mem = obj as *mut RcMem<T>;
                        Some(&mut (*rc_mem).rc as *mut GcRc)
                    },
                    #[cfg(not(feature = "freeze"))]
                    freeze: |_, _| unimplemented!("freeze"),
                    #[cfg(feature = "freeze")]
                    freeze: |p, into| unsafe {
                        use bincode::Options;
                        let obj = p as *mut T;
                        let opts = bincode::DefaultOptions::new();
                        let sz = opts.serialized_size(&*obj).unwrap();
                        opts.serialize_into(into, &*obj).unwrap();
                        sz as usize
                    },
                    clone: opt.clone,
                    fmt: delegate! { fmt(f) },
                })))
            }
        }
    }

    pub fn deep_clone(&self) -> Result<Object, Error> {
        let clonefn = self.vt.clone
                             .ok_or_else(|| error!(CloneNotImplemented,
                                                   obj: OpName::OpStr(self.vt.type_name)))?;
        Ok(unsafe { (clonefn)(self.mem) })
    }

    pub fn new<T: Userdata + 'static>(obj: T) -> Object {
        let layout = unsafe { ud_layout::<T>() };
        let vtable = Object::register::<T>(OptVTable::default());
        let mem = unsafe {
            let p = alloc(layout) as *mut T;
            if p.is_null() {
                handle_alloc_error(layout);
            }
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
        unsafe {
            if let Some(rc) = (self.vt.get_rc)(self.mem) {
                (*rc).0.load(atomic::Ordering::SeqCst)
            } else {
                1
            }
        }
    }

    pub fn cast_mut<T: 'static>(&self) -> Result<*mut T, Error> {
        if TypeId::of::<T>() != self.type_id {
            let expect_t = type_name::<T>();
            let actual_t = self.vt.type_name;
            let (expect_t, actual_t) = simplify_types(expect_t, actual_t);
            return Err(error!(STypeError,
                        expect: format!("(object {expect_t})"),
                        got: format!("(object {actual_t})"),)
                        .argn(0).bop(Builtin::Nil))
        }
        Ok(self.mem as *mut T)
    }

    pub fn cast<T: 'static>(&self) -> Result<*const T, Error> {
        Ok(self.cast_mut()? as *const T)
    }

    /// # Safety
    ///
    /// Must be the correct type, otherwise this is undefined behaviour.
    pub unsafe fn fastcast_mut<T: Userdata>(&mut self) -> *mut T {
        self.mem as *mut T
    }

    /// # Safety
    ///
    /// Must be the correct type, otherwise this is undefined behaviour.
    pub unsafe fn fastcast<T: Userdata>(&self) -> *const T {
        self.mem as *const T
    }

    pub fn from_ref<T: Userdata>(obj: &mut T) -> Object {
        macro_rules! delegate {($name:ident($($arg:ident),*)) => {
            |this, $($arg),*| unsafe { (*(this as *mut T)).$name($($arg),*) }
        }}
        let type_id = TypeId::of::<*mut T>();
        let vtables = get_vtables();
        let vt = match vtables.lock().unwrap().entry(type_id) {
            Entry::Occupied(vp) => *vp.get(),
            Entry::Vacant(entry) => {
                entry.insert(Box::leak(Box::new(VTable {
                    clone: None,
                    type_id: TypeId::of::<T>(),
                    type_name: type_name::<T>(),
                    drop: |_| {},
                    get_rc: |_| None,
                    #[cfg(not(feature = "freeze"))]
                    freeze: |_, _| unimplemented!("freeze"),
                    #[cfg(feature = "freeze")]
                    freeze: |p, into| unsafe {
                        use bincode::Options;
                        let obj = p as *mut T;
                        let opts = bincode::DefaultOptions::new();
                        let sz = opts.serialized_size(&*obj).unwrap();
                        opts.serialize_into(into, &*obj).unwrap();
                        sz as usize
                    },
                    fmt: delegate! { fmt(f) },
                })))
            },
        };
        Object {
            mem: obj as *mut T as *mut u8,
            type_id,
            vt,
        }
    }

    pub fn void_vtable() -> &'static VTable {
        let vtables = get_vtables();
        match vtables.lock().unwrap().entry(TypeId::of::<Voided>()) {
            Entry::Occupied(vp) => vp.get(),
            Entry::Vacant(entry) => {
                entry.insert(Box::leak(Box::new(VTable {
                    clone: None,
                    type_id: TypeId::of::<Void>(),
                    type_name: "void",
                    drop: |_| {},
                    get_rc: |_| None,
                    #[cfg(not(feature = "freeze"))]
                    freeze: |_, _| unimplemented!("freeze"),
                    #[cfg(feature = "freeze")]
                    freeze: |_, into| {
                        use bincode::Options;
                        let opts = bincode::DefaultOptions::new();
                        let sz = opts.serialized_size(&()).unwrap();
                        opts.serialize_into(into, &()).unwrap();
                        sz as usize
                    },
                    fmt: |_, f| write!(f, "void"),
                })))
            },
        }
    }

    pub fn void(&mut self) {
        self.type_id = TypeId::of::<Voided>();
        unsafe { (self.vt.drop)(self.mem) };
        self.vt = Self::void_vtable();
        self.mem = null_mut();
    }

    pub fn lock(&mut self) {
        self.type_id = TypeId::of::<Locked>();
    }

    pub fn unlock(&mut self) {
        self.type_id = self.vt.type_id;
    }

    pub fn is_locked(&self) -> bool {
        self.type_id == TypeId::of::<Locked>()
    }

    pub fn take<T: 'static>(&mut self) -> Result<T, Error> {
        let mut obj: MaybeUninit<T> = MaybeUninit::uninit();
        if self.type_id == TypeId::of::<Voided>() {
            return err!(TypeError, expect: Builtin::Object, got: Builtin::Void)
        }
        if self.type_id == TypeId::of::<Locked>() {
            return err!(MutLocked, vt: self.vt)
        }
        unsafe {
            let rc_mem = self.mem as *mut RcMem<T>;
            if !(*rc_mem).rc.is_owned() {
                return err!(CannotMoveSharedReference, vt: self.vt,
                            nref: (*rc_mem).rc.num_refs())
            }
            ptr::copy(self.cast()?, obj.as_mut_ptr(), 1);
            self.type_id = TypeId::of::<Voided>();
            dealloc(self.mem, ud_layout::<T>());
            self.vt = Self::void_vtable();
            self.mem = null_mut();
            Ok(obj.assume_init())
        }
    }
}

impl Traceable for Object {
    fn trace(&self, _gray: &mut Vec<*mut NkAtom>) {}

    fn update_ptrs(&mut self, _reloc: &PtrMap) {}
}

unsafe impl Send for Object {}

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
/// `Gc<T>` survives your VM getting dropped, so you can create a reference to
/// something that you intend for a VM to modify, and then keep the reference
/// after the VM is no longer necessary.
///
/// Remember that you have to actually run the VM occasionally for the GC to
/// eventually drop these references. If the `Gc<T>` has been dropped by your
/// Rust code and your SPAIK code the GC still needs to complete a cycle in
/// order to figure that out.
///
/// In order for `Gc<T>` to be `Send`/`Sync` it requires that `T` is too, it
/// doesn't do any synchronization magic on `T` itself.
pub struct Gc<T> where T: Userdata {
    this: *mut RcMem<T>,
}

unsafe impl<T: Sync + Send + Userdata> Send for Gc<T> {}
unsafe impl<T: Sync + Send + Userdata> Sync for Gc<T> {}

impl<T: Userdata> Gc<T> {
    /// # Why does this take an `Fn` instead of an `FnMut`?
    ///
    /// Because you should not be able to call `with` on a potentially aliased
    /// `Gc<T>` inside `with` recursively, then you could have multiple `&mut`
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
        with_ref!(self, Object(s) => {
            #[allow(clippy::unnecessary_cast)]
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
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct Continuation {
    stack: Vec<PV>,
    pub frame: usize,
    pub dip: usize,
}

impl Continuation {
    pub fn new(stack: Vec<PV>, frame: usize, dip: usize) -> Continuation {
        Continuation { stack, frame, dip }
    }

    pub fn inst(&self, s: &mut Vec<PV>) {
        s.clear();
        s.extend(self.stack.iter());
    }
}

impl Traceable for Continuation {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        for pv in self.stack.iter() {
            pv.trace(gray)
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        for pv in self.stack.iter_mut() {
            pv.update_ptrs(reloc)
        }
    }
}

impl LispFmt for Continuation {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "stack:")?;
        if self.stack.is_empty() {
            writeln!(f, "    (empty)")?;
        }
        for (idx, val) in self.stack.iter().enumerate().rev() {
            let (idx, frame) = (idx as i64, self.frame as i64);
            write!(f, "{}", if idx == frame { " -> " } else { "    " })?;
            write!(f, "{}: ", idx - frame)?;
            val.lisp_fmt(visited, f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct Intr {
    pub op: Builtin,
    pub arg: PV,
}

// #[derive(Copy, Clone, Debug)]
// #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
// pub struct Struct {
//     pub arg: ,
// }

impl LispFmt for Intr {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.op)?;
        self.arg.lisp_fmt(visited, f)
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
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct Void;

impl LispFmt for Void {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "void")
    }
}

#[cfg(feature = "math")]
fissile_types! {
    (Void, Builtin::Void, Void),
    (Cons, Builtin::Cons, crate::nkgc::Cons),
    (Intr, Builtin::Intr, crate::nuke::Intr),
    (Lambda, Builtin::Lambda, crate::nkgc::Lambda),
    (String, Builtin::String, std::string::String),
    (PV, Builtin::Ref, crate::nkgc::PV),
    (Vector, Builtin::Vector, Vec<PV>),
    (Table, Builtin::Table, FnvHashMap<PV, PV>),
    (Vec4, Builtin::Vec4, glam::Vec4),
    (Mat2, Builtin::Mat2, glam::Mat2),
    (Mat3, Builtin::Mat3, glam::Mat3),
    (Mat4, Builtin::Mat4, glam::Mat4),
    (Object, Builtin::Object, crate::nuke::Object),
    (Iter, Builtin::Iter, crate::nuke::Iter),
    (Continuation, Builtin::Continuation, crate::nuke::Continuation),
    (Subroutine, Builtin::Subr, Box<dyn crate::subrs::Subr>)
}

#[cfg(not(feature = "math"))]
fissile_types! {
    (Void, Builtin::Void, Void),
    (Cons, Builtin::Cons, crate::nkgc::Cons),
    (Intr, Builtin::Intr, crate::nuke::Intr),
    (Lambda, Builtin::Lambda, crate::nkgc::Lambda),
    (String, Builtin::String, std::string::String),
    (Table, Builtin::Table, FnvHashMap<PV, PV>),
    (PV, Builtin::Ref, crate::nkgc::PV),
    (Vector, Builtin::Vector, Vec<PV>),
    (Object, Builtin::Object, crate::nuke::Object),
    (Iter, Builtin::Iter, crate::nuke::Iter),
    (Continuation, Builtin::Continuation, crate::nuke::Continuation),
    (Subroutine, Builtin::Subr, Box<dyn crate::subrs::Subr>)
}

impl Traceable for FnvHashMap<PV, PV> {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        for (_k, v) in self.iter() {
            // XXX: Keys cannot be references, so they do not need to be traced
            v.trace(gray);
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        for (_k, v) in self.iter_mut() {
            // XXX: Keys cannot be references, so they do not need to be traced
            v.update_ptrs(reloc);
        }
    }
}

impl LispFmt for FnvHashMap<PV, PV> {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(table")?;
        for (k, v) in self.iter() {
            write!(f, " (")?;
            k.lisp_fmt(visited, f)?;
            write!(f, " . ")?;
            v.lisp_fmt(visited, f)?;
            write!(f, ")")?;
        }
        write!(f, ")")
    }
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
    ($($t:ty),*) => {$(impl $crate::nkgc::Traceable for $t {
        fn trace(&self, _gray: &mut Vec<*mut $crate::nuke::NkAtom>) {}
        fn update_ptrs(&mut self, _reloc: &$crate::nuke::PtrMap) {}
    })*};
}

#[cfg(feature = "math")]
trivial_trace!(glam::Vec2, glam::Vec3, glam::Vec4,
               glam::Mat2, glam::Mat3, glam::Mat4,
               glam::Quat);

trivial_trace!(Box<dyn subrs::Subr>, String, Void);

impl NkAtom {
    #[inline]
    pub fn make_ref<T: Fissile>(p: *mut T) -> PV {
        PV::Ref(NkAtom::make_raw_ref(p))
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn make_raw_ref<T: Fissile>(p: *mut T) -> *mut NkAtom {
        assert!(mem::size_of::<NkAtom>() <= ALIGNMENT);
        unsafe {
            (p as *mut u8).offset(-(ALIGNMENT as isize)) as *mut NkAtom
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

    pub fn full_size(&self) -> usize {
        mem::size_of::<NkAtom>() + self.sz as usize
    }
}

#[inline]
pub unsafe fn fastcast<T>(atom: *const NkAtom) -> *const T {
    const DELTA: isize = mem::size_of::<NkAtom>() as isize;
    let p = (atom as *const u8).offset(DELTA);
    align(p, ALIGNMENT) as *mut T
}

#[inline]
pub unsafe fn fastcast_mut<T>(atom: *mut NkAtom) -> *mut T {
    const DELTA: isize = mem::size_of::<NkAtom>() as isize;
    let p = (atom as *mut u8).offset(DELTA);
    align_mut(p, ALIGNMENT) as *mut T
}

#[inline]
pub unsafe fn atom_kind(atom: *const NkAtom) -> NkT {
    mem::transmute((*atom).meta.typ())
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
pub fn cast_mut_err<T: Fissile>(atom: *mut NkAtom) -> Result<*mut T, Error> {
    cast_mut(atom).ok_or_else(|| {
        error!(TypeError,
               expect: T::type_of().into(),
               got: unsafe { atom_kind(atom).into() })
    })
}

#[inline]
pub fn cast_err<T: Fissile>(atom: *const NkAtom) -> Result<*const T, Error> {
    cast_mut_err(atom as *mut NkAtom).map(|p| p as *const T)
}

#[inline]
pub unsafe fn destroy_atom(atom: *mut NkAtom) {
    DESTRUCTORS[(*atom).meta.typ() as usize](fastcast_mut::<u8>(atom));
}

pub unsafe fn deep_size_of_atom(atom: *const NkAtom) -> usize {
    let mut sz = (*atom).full_size();
    match to_fissile_ref(atom) {
        NkRef::Cons(cns) => {
            if let PV::Ref(p) = (*cns).car {
                sz += deep_size_of_atom(p);
            }
            if let PV::Ref(p) = (*cns).cdr {
                sz += deep_size_of_atom(p);
            }
        }
        NkRef::Intr(intr) => if let PV::Ref(p) = (*intr).arg {
            sz += deep_size_of_atom(p);
        },
        NkRef::PV(pv) => if let PV::Ref(p) = *pv { sz += deep_size_of_atom(p) },
        NkRef::Vector(xs) => {
            sz += (*xs).iter().map(|x| if let PV::Ref(p) = x {
                deep_size_of_atom(*p)
            } else {
                0
            }).sum::<usize>()
        }
        NkRef::Table(hm) => unsafe {
            sz += (*hm).iter().map(|(x, y)| {
                let mut s = 0;
                if let PV::Ref(p) = x { s += deep_size_of_atom(*p) }
                if let PV::Ref(p) = y { s += deep_size_of_atom(*p) }
                s
            }).sum::<usize>()
        },
        NkRef::Continuation(c) => {
            sz += (*c).stack.iter().map(|x| if let PV::Ref(p) = x {
                deep_size_of_atom(*p)
            } else {
                0
            }).sum::<usize>()
        },
        _ => ()
    }
    sz
}

pub fn clone_atom(mut atom: *const NkAtom, mem: &mut Arena) -> Result<*mut NkAtom, Error> {
    unsafe {
        atom = mem.mem_fit_bytes(atom, deep_size_of_atom(atom));
        clone_atom_rec(atom, mem)
    }
}

/// SAFETY: Must make sure the full recursive clone can fit in memory before calling
pub unsafe fn clone_atom_rec(atom: *const NkAtom, mem: &mut Arena) -> Result<*mut NkAtom, Error> {
    macro_rules! clone {
        ($x:expr) => {{
            let (rf, _) = mem.put(unsafe { (*$x).clone() });
            rf
        }};
    }
    Ok(match to_fissile_ref(atom) {
        NkRef::Void(v) => clone!(v),
        NkRef::Cons(cns) => {
            unsafe {
                let car = (*cns).car.deep_clone_unchecked(mem)?;
                let cdr = (*cns).cdr.deep_clone_unchecked(mem)?;
                let (rf, _) = mem.put(Cons { car, cdr });
                rf
            }
        },
        NkRef::Intr(intr) => {
            unsafe {
                let intr = Intr {
                    op: (*intr).op,
                    arg: (*intr).arg.deep_clone_unchecked(mem)?,
                };
                let (rf, _) = mem.put(intr);
                rf
            }
        }
        NkRef::Lambda(_l) => todo!(),
        NkRef::String(s) => clone!(s),
        NkRef::PV(_p) => todo!(),
        NkRef::Vector(xs) => unsafe {
            let nxs = (*xs).iter().map(|p| p.deep_clone_unchecked(mem)).collect::<Result<Vec<_>, _>>()?;
            let (rf, _) = mem.put(nxs);
            rf
        },
        NkRef::Table(hm) => unsafe {
            let nxs = (*hm).iter().map(|(k, v)| -> Result<_,Error> {
                Ok((*k, v.deep_clone_unchecked(mem)?))
            }).collect::<Result<FnvHashMap<_, _>,_>>()?;
            let (rf, _) = mem.put(nxs);
            rf
        },
        #[cfg(feature = "math")]
        NkRef::Vec4(v4) => clone!(v4),
        #[cfg(feature = "math")]
        NkRef::Mat2(m2) => clone!(m2),
        #[cfg(feature = "math")]
        NkRef::Mat3(m3) => clone!(m3),
        #[cfg(feature = "math")]
        NkRef::Mat4(m4) => clone!(m4),
        NkRef::Object(s) => {
            let (rf, _) = mem.put(unsafe { (*s).deep_clone()? });
            rf
        }
        NkRef::Iter(i) => clone!(i),
        NkRef::Continuation(_c) => bail!(CloneNotImplemented { obj: OpName::OpBt(Builtin::Continuation) }),
        NkRef::Subroutine(_s) => bail!(CloneNotImplemented { obj: OpName::OpBt(Builtin::Subr) }),
    })
}

#[allow(dead_code)]
pub struct Nuke {
    free: *mut u8,
    used: usize,
    num_frees: usize,
    num_allocs: usize,
    num_atoms: usize,
    sz: usize,
    reloc: PtrMap,
    last: *mut NkAtom,
    mem: *mut u8,
    #[cfg(not(target_arch = "wasm32"))]
    start_time: SystemTime,
}

const ALIGNMENT: usize = 16;

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
fn align_mut<T>(p: *mut T, a: usize) -> *mut T {
    sptr::Strict::with_addr(p, (((p as isize) + (a as isize) - 1) & !((a as isize) - 1))
                            as usize)
}
fn align<T>(p: *const T, a: usize) -> *const T {
    sptr::Strict::with_addr(p, (((p as isize) + (a as isize) - 1) & !((a as isize) - 1))
                            as usize)
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

pub unsafe fn malloc<T>(sz: usize) -> *mut T {
    let layout = Layout::array::<T>(sz).unwrap();
    let p = alloc(layout) as *mut T;
    if p.is_null() {
        handle_alloc_error(layout);
    }
    p
}

#[allow(dead_code)]
pub unsafe fn free<T>(p: *mut T, sz: usize) {
    dealloc(p as *mut u8, Layout::array::<T>(sz).unwrap())
}

#[must_use = "Relocation must be confirmed"]
pub struct RelocateToken;

impl Drop for RelocateToken {
    fn drop(&mut self) {
        panic!("Relocation of memory arena happened without updating pointers");
    }
}

impl Nuke {
    pub fn new(sz: usize) -> Nuke {
        log::trace!("new heap ...");
        vm_begin();

        assert!(sz >= 128, "Nuke too small");

        let layout = unsafe {
            Layout::from_size_align_unchecked(sz, ALIGNMENT)
        };

        let mut nk = Nuke {
            free: ptr::null_mut(),
            used: 0,
            num_frees: 0,
            num_allocs: 0,
            num_atoms: 0,
            sz,
            reloc: PtrMap(Vec::new()),
            last: ptr::null_mut(),
            mem: unsafe { alloc(layout) },
            #[cfg(not(target_arch = "wasm32"))]
            start_time: SystemTime::now(),
        };

        if nk.mem.is_null() {
            handle_alloc_error(layout);
        }

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
        log::trace!("compacting heap ...");

        let mut node = self.fst_mut();
        let mut npos;
        let mut start = node as *mut u8;

        loop {
            let next_node = (*node).next;
            npos = start as *mut NkAtom;
            let sz = (*node).full_size();
            if npos != node {
                self.reloc.push(node, npos);
                memmove(npos, node, sz);
            }
            start = align_mut(start.add(sz), ALIGNMENT);
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
        log::trace!("☢️💥");

        for atom in self.iter_mut() {
            unsafe { destroy_atom(atom) }
        }
        self.last = self.fst_mut();
        self.free = self.offset(mem::size_of::<NkAtom>());
        self.used = mem::size_of::<NkAtom>();
        (*self.fst_mut()).next = ptr::null_mut();
        self.num_atoms = 1;
    }

    pub unsafe fn sweep_compact(&mut self) -> RelocateToken {
        log::trace!("sweep-compacting heap ...");

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
                memmove(npos, node, sz);
            }

            (*npos).set_color(Color::White);
            start = align_mut(start.add(sz), ALIGNMENT);

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

    pub unsafe fn grow_realloc(&mut self, fit: usize) -> Option<RelocateToken> {
        log::trace!("growing heap ...");

        let new_sz = (self.sz << 1).max(self.sz + fit);
        let layout = Layout::from_size_align_unchecked(self.sz, ALIGNMENT);
        let old_mem = self.mem as usize;
        let mem = realloc(self.mem, layout, new_sz);
        if mem.is_null() {
            handle_alloc_error(layout);
        }
        self.mem = mem;
        self.sz = new_sz;
        if old_mem != self.mem as usize {
            let mut node = self.fst_mut();
            loop {
                let old_addr = old_mem + (node as usize - self.mem as usize);
                let np = sptr::Strict::with_addr(self.mem, old_addr);
                self.reloc.push(np, node);
                let old_next = (*node).next;
                if old_next.is_null() {
                    self.last = node;
                    self.free = (node as *mut u8).add((*node).full_size());
                    self.used = self.free as usize - self.mem as usize;
                    break;
                }
                let next = self.mem.add(old_next as usize - old_mem) as *mut NkAtom;
                (*node).next = next;
                node = next;
            }
            Some(RelocateToken)
        } else {
            None
        }
    }

    #[allow(dead_code)]
    pub fn assert_alignment(&self) {
        for atom in self.iter() {
            assert_eq!(atom as usize % align_of::<NkAtom>(), 0);
            assert_atom_inner_alignment(atom);
        }
    }

    #[allow(dead_code)]
    pub fn shallow_clone(&self) -> Nuke {
        let mut nk = Nuke::new(self.sz);

        let mut mem = nk.mem;
        let mut new_node = ptr::null_mut();
        let mut node = self.fst();
        unsafe {
            while !node.is_null() {
                let sz = (*node).full_size();
                memcpy(mem, node, sz);
                nk.reloc.push(node, mem);
                new_node = mem as *mut NkAtom;
                let nmem = mem.add(sz);
                mem = align_mut(nmem, ALIGNMENT);
                (*new_node).next = mem as *mut NkAtom;
                node = (*node).next;
            }
            (*new_node).next = ptr::null_mut();
        }
        nk.free = mem;
        nk.last = new_node;
        nk.used = self.used;
        nk.num_allocs = self.num_allocs;
        nk.num_atoms = self.num_atoms;
        #[cfg(not(target_arch = "wasm32"))] {
            nk.start_time = self.start_time;
        }

        nk
    }

    pub unsafe fn make_room(&mut self, fit: usize) -> Option<RelocateToken> {
        log::trace!("making room in heap ...");

        if self.used + fit > self.sz {
            self.grow_realloc(fit)
        } else {
            Some(self.compact())
        }
    }

    pub fn confirm_relocation(&mut self, t: RelocateToken) {
        mem::forget(t);
        self.reloc.0.clear();
    }

    pub fn fst_mut(&mut self) -> *mut NkAtom {
        self.mem as *mut NkAtom
    }

    pub fn fst(&self) -> *const NkAtom {
        self.mem as *const NkAtom
    }

    pub fn offset<T>(&mut self, n: usize) -> *mut T {
        unsafe {
            self.mem.add(n) as *mut T
        }
    }

    pub unsafe fn alloc<T: Fissile>(&mut self) -> (*mut NkAtom, *mut T, Option<RelocateToken>) {
        let max_padding = ALIGNMENT - 1;
        let max_sz = size_of::<T>() + size_of::<NkAtom>() + max_padding;
        let ret = if self.will_overflow(max_sz) {
            self.make_room(max_sz)
        } else {
            None
        };

        let cur = align_mut(self.free as *mut NkAtom, ALIGNMENT);
        let cur_diff = cur as usize - self.free as usize;
        self.used += cur_diff;

        let p = (cur as *mut u8).add(mem::size_of::<NkAtom>()) as *mut T;
        let pa = align_mut(p, ALIGNMENT);
        let pdiff = pa as usize - p as usize;
        let full_sz = mem::size_of::<T>()
                    + mem::size_of::<NkAtom>()
                    + pdiff;

        let last = self.last;
        self.last = cur;

        self.free = (cur as *mut u8).add(full_sz);
        self.used += full_sz;
        self.num_atoms += 1;
        self.num_allocs += 1;

        (*cur).next = ptr::null_mut();
        (*cur).sz = (full_sz - mem::size_of::<NkAtom>()) as NkSz;
        (*cur).init(T::type_of());
        debug_assert_eq!((cur as *mut u8).add((*cur).full_size()),
                         self.free);

        (*last).next = cur;

        (cur, pa, ret)
    }

    #[inline]
    pub fn size_of<T: Fissile>() -> usize {
        mem::size_of::<T>() + mem::size_of::<NkAtom>() + ALIGNMENT
    }

    pub fn will_overflow(&mut self, sz: usize) -> bool {
        self.free as usize + sz >= self.offset::<u8>(self.sz) as usize
    }

    #[inline]
    pub unsafe fn fit<T: Fissile>(&mut self, num: usize) -> Option<RelocateToken> {
        let full_sz = Nuke::size_of::<T>() * num;
        if self.will_overflow(full_sz) {
            self.make_room(full_sz)
        } else {
            None
        }
    }

    #[inline]
    pub unsafe fn fit_bytes(&mut self, sz: usize) -> Option<RelocateToken> {
        if self.will_overflow(sz) {
            self.make_room(sz)
        } else {
            None
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

impl Drop for Nuke {
    fn drop(&mut self) {
        unsafe {
            self.destroy_the_world();
            let layout = Layout::from_size_align_unchecked(self.sz, ALIGNMENT);
            dealloc(self.mem, layout);
            vm_end();
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
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        unimplemented!()
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

pub const META_COLOR_MASK: u8 = 0x03;
pub const META_TYPE_MASK: u8 = 0xfc;

pub struct AtomMeta(pub u8);

#[repr(C)]
pub struct NkAtom {
    next: *mut NkAtom,
    sz: NkSz,
    pub(crate) meta: AtomMeta,
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

#[derive(Debug, Default)]
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
    use std::num::IntErrorKind;

    #[cfg(feature = "derive")]
    use spaik_proc_macros::Userdata;
    use spaik_proc_macros::{Obj, methods, hooks};

    use crate::{Spaik, r8vm::{R8VM, ArgSpec}, Lispify, Lambda, FromLisp3, error::{Source, ErrorKind}, __spaik_call_builder::IntoCallBuilder, LinkedEvents};

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

    #[cfg(feature = "derive")]
    #[test]
    fn userdata_ref() {
        use spaik_proc_macros::Userdata;

        #[derive(Debug, Clone, Userdata)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        struct Data {
            x: String
        }
        let _data = Data { x: String::from("something") };
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (f x) (println x))").unwrap();
        // vm.call("f", (&mut data,));
    }

    #[test]
    fn clone_obj() {
        #[derive(Debug, Clone, Obj)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        struct Obj(i32);
        #[methods(())]
        impl Obj {
            fn doit(_take: Obj) -> i32 { 1 }
        }
        let mut vm = Spaik::new_no_core();
        vm.defobj(Obj::vtable().can_clone());
        vm.defstatic::<Obj, ()>();
        vm.set("obj", Obj(1));
        vm.exec("(obj/doit obj)").unwrap();
        vm_assert!(vm, "(void? obj)");
        vm.set("obj", Obj(1));
        vm_assert!(vm, "(not (void? obj))");
        vm.exec("(obj/doit (clone obj))").unwrap();
        vm_assert!(vm, "(not (void? obj))");
    }

    #[test]
    fn static_method_err_thing() {
        #[derive(Debug, Clone, Obj)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        struct Obj(i32);
        #[methods(())]
        impl Obj {
            fn doit() -> Result<i32, Error> { Ok(1) }
            fn doitwrong() -> Result<i32, Error> {
                bail!(SomeError { msg: "lmao".to_string() })
            }
        }
        let mut vm = Spaik::new_no_core();
        vm.defobj(Obj::vtable().can_clone());
        vm.defstatic::<Obj, ()>();
        vm.set("obj", Obj(1));
        assert_eq!(vm.eval("(obj/doit)"), Ok(1i32));
        let l: Result<i32, Error> = vm.eval("(obj/doitwrong)");
        let mut r: Result<i32, Error> = err!(SomeError, msg: "lmao".to_string());
        r = r.map_err(|e| e.src(Source::new(1, 0, None)));
        assert_eq!(l.map_err(|e| e.cause().clone()), r);
    }

    #[test]
    fn callbacks_in_methods() {
        #[derive(Debug, Clone, Obj)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        struct Obj(i32);
        #[methods(())]
        impl Obj {
            fn doit(&mut self, x: i32, mut myfunk: impl FnMut(i32) -> Result<i32, Error>) -> Result<i32, Error> {
                myfunk(1 + x)
            }
            fn doitb(&mut self, mut myfunk: impl FnMut() -> Result<bool, Error>) -> Result<bool, Error> {
                myfunk()
            }
            fn sdoit(x: i32, mut myfunk: impl FnMut(i32) -> Result<i32, Error>) -> Result<i32, Error> {
                myfunk(1 + x)
            }
            fn f(&mut self) -> i32 {
                1
            }
        }
        #[hooks("")]
        trait TIFACE {
            fn test1() -> i32;
            fn test2() -> i32;
            fn test3(bob: &mut Obj) -> i32;
            fn test4(bob: &mut Obj) -> bool;
            fn test5(bob: &mut Obj) -> bool;
            fn test6(bob: &mut Obj) -> bool;
            fn test7() -> i32;
        }
        let mut vm = Spaik::new_no_core();
        vm.defobj(Obj::vtable());
        vm.defmethods::<Obj, ()>();
        vm.bind_resource_fns::<Obj, ()>(None);
        vm.set("obj", Obj(1));
        assert_eq!(vm.eval("(obj :doit 2 (lambda (x) (+ x 2)))"), Ok(5i32));
        assert_eq!(vm.eval("(obj :doit 2 (lambda (x) (+ x 2))) (if (void? obj) (error 'err))"),
                   Ok(()));

        vm.exec("(define (test-1) (obj/doit 2 (lambda (x) (+ x 2))))").unwrap();
        vm.exec("(define (doit) (obj/doit 2 (lambda (x) (+ x 2))))").unwrap();
        vm.exec("(define (test-2) (doit) (doit) (doit))").unwrap();
        vm.exec("(define (test-3 obj) (obj :doit 3 (lambda (x) (+ x 4))))").unwrap();
        vm.exec("(define (test-4 obj) (obj :doitb (lambda () (void? obj))))").unwrap();
        vm.exec("(define (test-5 obj) (obj :doitb (lambda () (mut-locked? obj))))").unwrap();
        vm.exec("(define (test-6 obj) (obj :doitb (lambda () (obj :f))))").unwrap();
        vm.exec("(define (test-7) (obj/sdoit 3 (lambda (x) (+ x 4))))").unwrap();
        let mut bobj = Obj(2);
        let mut hooks = TIFACE::default();
        hooks.link_events(&mut vm);
        assert_eq!(hooks.on(&mut vm).with_resource(&mut bobj).test1(), Ok(5));
        assert_eq!(hooks.on(&mut vm).with_resource(&mut bobj).test2(), Ok(5));
        assert_eq!(hooks.on(&mut vm).test3(&mut bobj), Ok(8));
        assert_eq!(hooks.on(&mut vm).test4(&mut bobj), Ok(false));
        assert_eq!(hooks.on(&mut vm).test5(&mut bobj), Ok(true));
        let res: Result<bool, Error> = hooks.on(&mut vm).test6(&mut bobj);
        assert!(matches!(res.map_err(|e| e.cause().kind().clone()),
                         Err(ErrorKind::MutLocked { .. })));
        assert_eq!(hooks.on(&mut vm).test7(), Ok(8i32));
        // hooks.on(&mut vm).test6(&mut bobj).unwrap();
    }
}
