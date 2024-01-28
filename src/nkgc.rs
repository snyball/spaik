//! The Nuclear Garbage Collector

use crate::builtins::{Builtin, BUILTIN_SYMS};
use crate::r8vm::{RuntimeError, ArgSpec};
use crate::nuke::{*, self};
use crate::error::{ErrorKind, Error, Source};
use crate::fmt::{LispFmt, VisitSet};
use crate::subrs::FromLisp;
use crate::swym::{SwymDb, SymRef};
use std::any::TypeId;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::sync::mpsc::{Receiver, Sender, channel};
use fnv::FnvHashMap;
#[cfg(feature = "math")]
use glam::{Vec2, Vec3};
use serde::{Serialize, Deserialize};
use std::fmt::{self, Debug};
use std::{str, char};
use std::ptr::{self, addr_of};
use std::time::Duration;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::borrow::Cow;

macro_rules! __with_ref_common {
    ($ref:ident($ptr:ident) => $get:expr,
     $pv:expr,
     $($t:ident($m:pat) => $action:block),+) => {{
         #[allow(unused_unsafe)]
         unsafe {
             let err = || $crate::error::Error::new(
                 $crate::error::ErrorKind::TypeNError {
                     expect: vec![
                         $($crate::nuke::NkT::$t.into()),+
                     ],
                     got: $pv.bt_type_of(),
                 }
             );
             match $pv {
                 #[allow(unused_unsafe)]
                 $crate::nkgc::PV::Ref($ptr) => match $get {
                     $($crate::nuke::$ref::$t($m) => $action,)+
                         _ => Err(err())
                 }
                 _ => Err(err())
             }
         }
     }}
}


macro_rules! with_ref {
    ($pv:expr, $($t:ident($m:pat) => $action:block),+) => {
        __with_ref_common!(NkRef(p) => $crate::nuke::to_fissile_ref(p),
                           $pv, $($t($m) => $action),+)
    };
}

macro_rules! with_ref_mut {
    ($pv:expr, $($t:ident($m:pat) => $action:block),+) => {
        __with_ref_common!(NkMut(p) => $crate::nuke::to_fissile_mut(p),
                           $pv, $($t($m) => $action),+)
    };
}

pub trait SymTypeOf {
    fn sym_type_of(&self) -> SymID;
}

pub trait Traceable {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>);
    fn update_ptrs(&mut self, reloc: &PtrMap);
}

pub struct ObjRef<T>(pub T);

impl<T: Userdata> TryFrom<PV> for ObjRef<*const T> {
    type Error = Error;

    fn try_from(v: PV) -> Result<ObjRef<*const T>, Self::Error> {
        Ok(ObjRef(with_ref!(v, Object(v) => {
            ObjPtr(v).cast::<T>()
        })?))
    }
}

impl<'a, T: Userdata> TryFrom<PV> for ObjRef<&'a T> {
    type Error = Error;

    fn try_from(v: PV) -> Result<ObjRef<&'a T>, Self::Error> {
        Ok(ObjRef(with_ref!(v, Object(v) => {
            ObjPtr(v).cast::<T>().map(|p| &*p)
        })?))
    }
}

impl<'a, T: Userdata> TryFrom<PV> for ObjRef<&'a mut T> {
    type Error = Error;

    fn try_from(v: PV) -> Result<ObjRef<&'a mut T>, Self::Error> {
        Ok(ObjRef(with_ref_mut!(v, Object(v) => {
            ObjPtrMut(v).cast_mut::<T>().map(|p| &mut *p)
        })?))
    }
}

impl<T,E> FromLisp<T> for PV where T: TryFrom<PV, Error = E>, E: Into<Error> {
    fn from_lisp(self, _mem: &mut Arena) -> Result<T, Error> {
        self.try_into().map_err(|e: E| e.into())
    }
}

impl TryFrom<PV> for String {
    type Error = Error;

    fn try_from(v: PV) -> Result<Self, Self::Error> {
        with_ref!(v, String(s) => {
            Ok((*s).clone())
        })
    }
}

impl<T: Userdata> TryFrom<PV> for ObjRef<*mut T> {
    type Error = Error;

    fn try_from(v: PV) -> Result<ObjRef<*mut T>, Self::Error> {
        Ok(ObjRef(with_ref_mut!(v, Object(v) => {
            ObjPtrMut(v).cast_mut::<T>()
        })?))
    }
}

impl LispFmt for String {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Symbol ID
pub use crate::swym::SymID;

impl fmt::Display for SymID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.as_ref())
    }
}

pub type Int = isize;
pub type Float = f32;

/// Primitive values
#[derive(Debug, Copy, Clone, Default)]
pub enum PV {
    Ref(*mut NkAtom),
    Sym(SymID),
    Int(Int),
    UInt(usize),
    Real(Float),
    Bool(bool),
    Char(char),
    #[cfg(feature = "shipyard")]
    Id(shipyard::EntityId),
    #[cfg(not(feature = "shipyard"))]
    Id(usize),
    #[cfg(feature = "math")]
    Vec2(Vec2),
    #[cfg(feature = "math")]
    Vec3(Vec3),
    #[default]
    Nil,
}

impl<'de> Deserialize<'de> for PV {
    fn deserialize<D>(_d: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        todo!()
    }
}

impl Serialize for PV {
    fn serialize<S>(&self, _d: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        todo!()
    }
}

impl PartialEq for PV {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Sym(l0), Self::Sym(r0)) => l0 == r0,
            (Self::Int(l0), Self::Int(r0)) => l0 == r0,
            (Self::UInt(l0), Self::UInt(r0)) => l0 == r0,
            (Self::Real(l0), Self::Real(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::Char(l0), Self::Char(r0)) => l0 == r0,
            (Self::Id(x), Self::Id(y)) => x == y,
            #[cfg(feature = "math")] (Self::Vec2(x), Self::Vec2(y)) => x == y,
            #[cfg(feature = "math")] (Self::Vec3(x), Self::Vec3(y)) => x == y,
            (Self::Ref(l), Self::Ref(r)) => unsafe {
                let tl = atom_kind(*l);
                if tl == NkT::String && tl == atom_kind(*r) {
                    let sl = fastcast::<String>(*l);
                    let sr = fastcast::<String>(*r);
                    (*sl).eq(&*sr)
                } else if tl == NkT::Intr && tl == atom_kind(*r) {
                    let sl = fastcast::<Intr>(*l);
                    let sr = fastcast::<Intr>(*r);
                    (*sl).arg.eq(&(*sr).arg) && (*sl).op == (*sr).op
                } else {
                    l == r
                }
            }
            (Self::Nil, Self::Nil) => true,
            (_, _) => false,
        }
    }
}

impl Eq for PV {}

impl TryFrom<PV> for f64 {
    type Error = crate::error::Error;

    fn try_from(value: PV) -> Result<Self, Self::Error> {
        if let PV::Real(v) = value {
            Ok(v as f64)
        } else {
            err!(TypeError,
                 expect: Builtin::Float,
                 got: value.bt_type_of())
        }
    }
}

impl From<bool> for PV {
    fn from(value: bool) -> Self {
        PV::Bool(value)
    }
}

impl TryFrom<PV> for SymID {
    type Error = Error;
    fn try_from(value: PV) -> Result<Self, Self::Error> {
        if let PV::Sym(sid) = value {
            Ok(sid)
        } else {
            err!(TypeError,
                 expect: Builtin::Symbol,
                 got: value.bt_type_of())
        }
    }
}

impl fmt::Display for PV {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self as &dyn LispFmt)
    }
}

impl Traceable for PV {
    #[inline]
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        if let PV::Ref(ptr) = *self {
            mark_atom(ptr, gray)
        }
    }

    #[inline]
    fn update_ptrs(&mut self, reloc: &PtrMap) {
        if let PV::Ref(ref mut ptr) = self {
            *ptr = reloc.get(*ptr) as *mut NkAtom;
        }
    }
}

macro_rules! num_op {
    ($name:ident, $sym:tt, $op:tt) => {
        pub fn $name(&self, o: &PV) -> Result<PV, Error> {
            use PV::*;
            Ok(match (self, o) {
                (Int(x), Real(y)) => Real(*x as f32 $op y),
                (Int(x), Int(y)) => Int(x $op y),
                (Real(x), Int(y)) => Real(x $op *y as f32),
                (Real(x), Real(y)) => Real(x $op y),
                #[cfg(feature = "math")] (Real(x), Vec2(y)) => Vec2(*x $op *y),
                #[cfg(feature = "math")] (Vec2(x), Real(y)) => Vec2(*x $op *y),
                #[cfg(feature = "math")] (Int(x), Vec2(y)) => Vec2(*x as f32 $op *y),
                #[cfg(feature = "math")] (Vec2(x), Int(y)) => Vec2(*x $op *y as f32),
                #[cfg(feature = "math")] (Real(x), Vec3(y)) => Vec3(*x $op *y),
                #[cfg(feature = "math")] (Vec3(x), Real(y)) => Vec3(*x $op *y),
                #[cfg(feature = "math")] (Int(x), Vec3(y)) => Vec3(*x as f32 $op *y),
                #[cfg(feature = "math")] (Vec3(x), Int(y)) => Vec3(*x $op *y as f32),
                #[cfg(feature = "math")] (Vec2(x), Vec2(y)) => Vec2(*x $op *y),
                #[cfg(feature = "math")] (Vec3(x), Vec3(y)) => Vec3(*x $op *y),
                (x, y) =>
                    return Err(error!(IfaceNotImplemented,
                                      got: vec![x.type_of().into(), y.type_of().into()])
                               .bop(Builtin::$sym))
            })
        }
    };
}

macro_rules! inplace_num_op {
    ($name:ident, $sym:tt, $op:tt, $op_inplace:tt) => {
        pub fn $name(&mut self, o: &PV) -> Result<(), Error> {
            use PV::*;
            match (&mut *self, o) {
                (Int(x), Real(y)) => *self = Real(*x as f32 $op y),
                (Int(x), Int(y)) => *x $op_inplace y,
                (Real(x), Int(y)) => *x $op_inplace *y as f32,
                (Real(x), Real(y)) => *x $op_inplace y,
                #[cfg(feature = "math")] (Vec2(x), Vec2(y)) => *x $op_inplace *y,
                #[cfg(feature = "math")] (Vec3(x), Vec3(y)) => *x $op_inplace *y,
                #[cfg(feature = "math")] (Vec2(x), Real(y)) => *x $op_inplace *y,
                #[cfg(feature = "math")] (Vec2(x), Int(y)) => *x $op_inplace *y as f32,
                #[cfg(feature = "math")] (Vec3(x), Real(y)) => *x $op_inplace *y,
                #[cfg(feature = "math")] (Vec3(x), Int(y)) => *x $op_inplace *y as f32,
                (x, y) =>
                    return Err(error!(IfaceNotImplemented,
                                      got: vec![x.type_of().into(), y.type_of().into()])
                               .bop(Builtin::$sym))
            }
            Ok(())
        }
    };
}

macro_rules! cmp_op {
    ($name:ident, $sym:tt, $($ordering:pat),*) => {
        pub fn $name(&self, o: &PV) -> Result<PV, Error> {
            use Ordering::*;
            match self.partial_cmp(o) {
                None => return Err(error!(IfaceNotImplemented,
                                          got: vec![self.type_of().into(), o.type_of().into()])
                                   .bop(Builtin::$sym)),
                $(Some($ordering) => Ok(PV::Bool(true)),)*
                _ => Ok(PV::Bool(false))
            }           
        }
    };
}

#[derive(Clone, Copy)]
struct PVVecIter {
    vec: *mut NkAtom,
    idx: usize,
}

impl Traceable for PVVecIter {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        mark_atom(self.vec, gray)
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        self.vec = reloc.get(self.vec) as *mut NkAtom;
    }
}

impl PVVecIter {
    fn new(vec: PV) -> PVVecIter {
        if let PV::Ref(ptr) = vec {
            if unsafe { atom_kind(ptr) } != NkT::Vector {
                panic!("Attempted to create PVVecIter from non-vector");
            }
            PVVecIter { vec: ptr, idx: 0 }
        } else {
            panic!("Attempted to create PVVecIter from non-vector");
        }
    }
}

impl Iterator for PVVecIter {
    type Item = PV;

    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.idx;
        self.idx += 1;
        unsafe {
            (*fastcast::<Vec<PV>>(self.vec)).get(idx).copied()
        }
    }
}

pub enum Quasi {
    USplice(PV),
    Unquote(PV),
}

pub enum QuasiMut {
    USplice(*mut PV),
    Unquote(*mut PV),
}

impl PV {
    pub fn is_zero(&self) -> bool {
           *self == PV::Int(0)
        || *self == PV::Real(0.0)
        || *self == PV::UInt(0)
    }

    pub fn type_of(&self) -> SymID {
        self.bt_type_of().sym_id()
    }

    pub fn str(&self) -> Cow<str> {
        with_ref!(*self, String(s) => {
            Ok(Cow::Borrowed(&(*s)[..]))
        }).unwrap_or_else(|_| {
            Cow::from(self.to_string())
        })
    }

    pub fn inner(self) -> Result<PV, Error> {
        let expect = ArgSpec::normal(1);
        let err = |n| move || error!(ArgError, expect, got_num: n);
        let mut it = self.args();
        let inner = it.next().ok_or_else(err(0))?;
        let extra = it.count();
        if extra > 0 {
            Err(err(1 + extra as u32)())
        } else {
            Ok(inner)
        }
    }

    pub fn set_inner(&mut self, v: PV) -> Result<PV, Error> {
        with_ref_mut!(*self, Cons(p) => {
            with_ref_mut!((*p).cdr, Cons(p) => {
                let pre = (*p).car;
                (*p).car = v;
                Ok(pre)
            })
        })
    }

    #[inline]
    pub fn tag(&self, mem: &mut Arena, tag: Source) {
        if let PV::Ref(p) = *self { mem.tag(p, tag) }
    }

    pub fn real(&self) -> Result<f32, Error> {
        match self {
            PV::Int(x) => Ok(*x as f32),
            PV::Real(x) => Ok(*x),
            _ => err!(TypeError,
                      expect: Builtin::Number,
                      got: self.bt_type_of())

        }
    }

    pub fn bt_type_of(&self) -> Builtin {
        use PV::*;
        match *self {
            Bool(_) => Builtin::Bool,
            Int(_) => Builtin::Integer,
            UInt(_) => Builtin::UnsignedInteger,
            Real(_) => Builtin::Float,
            Sym(_) => Builtin::Symbol,
            Char(_) => Builtin::Char,
            Id(_) => Builtin::Id,
            #[cfg(feature = "math")] Vec2(_) => Builtin::Vec2,
            #[cfg(feature = "math")] Vec3(_) => Builtin::Vec3,
            Ref(p) => unsafe {
                Builtin::from_sym(atom_kind(p).into()).expect("
                    Builtin datatype does not have builtin symbol"
                )
            },
            Nil => Builtin::Nil
        }
    }

    pub fn is_ref(&self) -> bool {
        matches!(self, PV::Ref(_))
    }

    pub fn rf(&self) -> Option<*mut NkAtom> {
        let PV::Ref(p) = *self else { return None };
        Some(p)
    }

    pub fn set_op(&mut self, op: Builtin) {
        self.rf()
            .and_then(cast_mut::<Cons>)
            .map(|cell| unsafe { (*cell).car = PV::Sym(op.sym_id()) })
            .unwrap();
    }

    pub fn make_iter(&self) -> Result<nuke::Iter, Error> {
        type IT = Box<dyn CloneIterator<Item = PV>>;
        macro_rules! e {() => {
            Err(error!(TypeNError,
                       expect: vec![Builtin::Cons, Builtin::String, Builtin::Vector],
                       got: self.bt_type_of()).bop(Builtin::Iter))
        };}
        let it: Box<dyn CloneIterator<Item = PV>> = match *self {
            PV::Nil => Box::new(PVIter { item: *self }),
            PV::Ref(p) => match to_fissile_ref(p) {
                NkRef::Cons(_) => {
                    let it: IT = Box::new(PVIter { item: *self });
                    it
                },
                // XXX: SAFETY: This is safe because strings are immutable,
                //              and std::slice::Iter maintains a pointer into
                //              the array that String refers to, not to the
                //              String struct itself, which may move.
                NkRef::String(xs) => {
                    #[derive(Clone)]
                    struct Wrapper<T> where T: Iterator + Clone {
                        p: *const NkAtom,
                        it: T,
                    }
                    impl<T> Traceable for Wrapper<T> where T: Iterator + Clone {
                        fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
                            gray.push(self.p as *mut NkAtom);
                        }
                        fn update_ptrs(&mut self, reloc: &PtrMap) {
                            self.p = reloc.get(self.p);
                        }
                    }
                    impl<T, V> Iterator for Wrapper<T> where T: Iterator<Item = V>  + Clone{
                        type Item = V;

                        fn next(&mut self) -> Option<Self::Item> {
                            self.it.next()
                        }
                    }
                    unsafe {
                        let it = (*xs).chars().map(PV::Char);
                        let it: IT = Box::new(Wrapper{p, it});
                        it
                    }
                },
                // XXX: SAFETY: This is safe because PVVecIter implements
                //              Traceable and will update the pointer on GC
                //              compacting. It does *not* refer directly to
                //              the internal array because it may be mutated
                //              and reallocated.
                NkRef::Vector(_) => {
                    let it: IT = Box::new(PVVecIter::new(*self));
                    it
                }
                _ => return e!(),
            }
            _ => return e!(),
        };

        Ok(nuke::Iter::new(*self, it))
    }

    pub fn iter(&self) -> PVIter {
        PVIter { item: *self }
    }

    pub fn iter_src<'b>(&self, nk: &'b Arena, src: Source) -> PVIterSrc<'b> {
        PVIterSrc { item: *self, src, nk }
    }

    pub fn ref_inner(&self) -> Result<*mut NkAtom, Error> {
        match self {
            PV::Ref(p) => Ok(*p),
            _ => err!(TypeError, expect: Builtin::Ref, got: self.bt_type_of())
        }
    }

    pub fn cons_iter(&self) -> impl Iterator<Item = ConsElem> {
        ConsIter { item: *self }
    }

    pub fn with_cell(&self, f: fn(PV, PV) -> PV) -> Option<PV> {
        with_ref!(*self, Cons(p) => { Ok(f((*p).car, (*p).cdr)) }).ok()
    }

    #[inline]
    pub fn car(&self) -> Option<PV> {
        self.with_cell(|car, _| car)
    }

    #[inline]
    pub fn cdr(&self) -> Option<PV> {
        self.with_cell(|_, cdr| cdr)
    }

    /// Returns Some(sym) if the PV is an application of `sym`.
    #[inline]
    pub fn op(&self) -> Option<SymID> {
        if self.is_atom() {
            return None;
        }
        match self.iter().next() {
            Some(PV::Sym(x)) => Some(x),
            _ => None,
        }
    }

    #[inline]
    pub fn bt_op(&self) -> Option<Builtin> {
        self.op().and_then(Builtin::from_sym)
    }

    #[inline]
    pub fn intr_mut(&self) -> Option<(Builtin, *mut PV)> {
        let PV::Ref(p) = *self else { return None };
        (unsafe{atom_kind(p)} == NkT::Intr).then(|| unsafe {
            let intr = fastcast_mut::<Intr>(p);
            ((*intr).op, (ptr::addr_of_mut!((*intr).arg)))
        })
    }

    pub fn quasi_mut(&self) -> Option<QuasiMut> {
        self.intr_mut().and_then(|(op, arg)| Some(match op {
            Builtin::USplice => QuasiMut::USplice(arg),
            Builtin::Unquote => QuasiMut::Unquote(arg),
            _ => return None
        }))
    }

    pub fn intr_set_inner(&mut self, p: PV) {
        self.intr_mut().map(|(_, arg)| unsafe { *arg = p });
    }

    #[inline]
    pub fn intr(&self) -> Option<(Builtin, PV)> {
        self.intr_mut().map(|(op, arg)| unsafe { (op, *arg) })
    }

    pub fn quasi(&self) -> Option<Quasi> {
        self.intr().and_then(|(op, arg)| Some(match op {
            Builtin::USplice => Quasi::USplice(arg),
            Builtin::Unquote => Quasi::Unquote(arg),
            _ => return None
        }))
    }

    #[inline]
    pub fn sym(&self) -> Result<SymID, Error> {
        Ok(match *self {
            PV::Sym(sym) => sym,
            _ => return err!(TypeError,
                             expect: Builtin::Symbol,
                             got: self.bt_type_of()),
        })
    }

    #[inline]
    pub fn args(&self) -> impl Iterator<Item = PV> {
        self.iter().skip(1)
    }

    pub fn is_atom(&self) -> bool {
        match *self {
            PV::Ref(p) => !matches!(unsafe{atom_kind(p)}, NkT::Cons),
            _ => true
        }
    }

    pub fn is_list(&self) -> bool {
        use PV::*;
        match *self {
            Nil => true,
            Ref(p) => unsafe { atom_kind(p) == NkT::Cons },
            _ => false,
        }
    }

    pub fn append(&mut self, new_tail: PV) -> Result<(), Error> {
        let e = 'err: {
            let PV::Ref(p) = *self else { break 'err *self };
            unsafe {
                let Some(mut cell) = cast_mut::<Cons>(p) else { break 'err *self };
                while (*cell).cdr != PV::Nil {
                    let pv = (*cell).cdr;
                    if pv == PV::Nil { break }
                    let PV::Ref(p) = pv else { break 'err pv };
                    let Some(ncell) = cast_mut::<Cons>(p) else { break 'err pv };
                    cell = ncell;
                }
                (*cell).cdr = new_tail;
                return Ok(())
            }
        };
        Err(ErrorKind::TypeError { expect: Builtin::Cons,
                                   got: e.bt_type_of() }.into())
    }

    // TODO: Create force_real, force_bool, etc, as well as int()->Option<i64>
    // Do it using some simple macros, that implement a trait called `PVT`
    pub fn force_int(&self) -> isize {
        // FIXME: Should use mem::transmute funny-business instead
        match self {
            PV::Int(x) => *x,
            _ => panic!("Expected PV::Int")
        }
    }

    pub fn force_uint(&self) -> usize {
        match self {
            PV::UInt(x) => *x,
            x => panic!("Expected PV::UInt, got: {:?}", x)
        }
    }

    pub fn equalp(&self, other: &PV) -> bool {
        unsafe {
            match (*self, other) {
                (PV::Ref(u), PV::Ref(v)) => match (to_fissile_ref(u),
                                                   to_fissile_ref(*v)) {
                    (NkRef::String(u), NkRef::String(v)) => u == v,
                    (NkRef::Cons(mut u), NkRef::Cons(mut v)) => loop {
                        if !(*u).car.equalp(&(*v).car) { break false }
                        let PV::Ref(u_next) = (*u).cdr else {
                            break (*u).cdr.equalp(&(*v).cdr);
                        };
                        let PV::Ref(v_next) = (*v).cdr else {
                            break (*u).cdr.equalp(&(*v).cdr);
                        };
                        let Some(u_next) = cast::<Cons>(u_next) else {
                            break (*u).cdr.equalp(&(*v).cdr);
                        };
                        let Some(v_next) = cast::<Cons>(v_next) else {
                            break (*u).cdr.equalp(&(*v).cdr);
                        };
                        u = u_next;
                        v = v_next;
                    }
                    (NkRef::PV(u), NkRef::PV(v)) => (*u).equalp(&*v),
                    (NkRef::Vector(u), NkRef::Vector(v)) =>
                        (*u).len() == (*v).len() &&
                        (*u).iter().zip((*v).iter()).all(|(u, v)| u.equalp(v)),
                    _ => u == *v,
                },
                _ => *self == *other
            }
        }
    }

    num_op!(add, Add, +);
    num_op!(sub, Sub, -);
    num_op!(div, Div, /);
    num_op!(mul, Mul, *);

    inplace_num_op!(add_mut, Add, +, +=);
    inplace_num_op!(sub_mut, Sub, -, -=);
    inplace_num_op!(mul_mut, Mul, *, *=);
    inplace_num_op!(div_mut, Mul, /, /=);

    pub fn pow(&self, o: &PV) -> Result<PV, Error> {
        use PV::*;
        Ok(match (self, o) {
            (Int(x), Real(y)) => Real((*x as f32).powf(*y)),
            (Int(x), Int(y)) => Int(x.pow(*y as u32)),
            (Real(x), Int(y)) => Real(x.powi(*y as i32)),
            (Real(x), Real(y)) => Real(x.powf(*y)),
            (x, y) => return Err(error!(ArgTypeError,
                                        expect: vec![Builtin::Number,
                                                     Builtin::Number],
                                        got: vec![x.bt_type_of(), y.bt_type_of()])
                                 .bop(Builtin::Pow))
        })
    }

    pub fn modulo(&self, o: &PV) -> Result<PV, Error> {
        use PV::*;
        Ok(match (self, o) {
            (Int(x), Int(y)) => Int(x % y),
            (x, y) => return Err(error!(ArgTypeError,
                                        expect: vec![Builtin::Number,
                                                     Builtin::Number],
                                        got: vec![x.bt_type_of(), y.bt_type_of()])
                                 .bop(Builtin::Modulo))
        })
    }


    cmp_op!(lt, Lt, Less);
    cmp_op!(gt, Gt, Greater);
    cmp_op!(lte, Lte, Less, Equal);
    cmp_op!(gte, Gte, Greater, Equal);

    pub fn deep_clone(self, mem: &mut Arena) -> PV {
        match self {
            PV::Ref(p) => PV::Ref(clone_atom(p, mem)),
            x => x,
        }
    }
}

impl PartialOrd for PV {
    fn partial_cmp(&self, other: &PV) -> Option<Ordering> {
        match (*self, *other) {
            (PV::Int(x), PV::Real(y)) => (x as f32).partial_cmp(&y),
            (PV::Int(x), PV::Int(y)) => Some(x.cmp(&y)),
            (PV::Real(x), PV::Real(y)) => x.partial_cmp(&y),
            (PV::Real(x), PV::Int(y)) => x.partial_cmp(&(y as f32)),
            (PV::Ref(l), PV::Ref(r)) => unsafe {
                let tl = atom_kind(l);
                if tl == NkT::String && tl == atom_kind(r) {
                    let sl = fastcast::<String>(l);
                    let sr = fastcast::<String>(r);
                    Some((*sl).cmp(&*sr))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl Hash for PV {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match *self {
            PV::Sym(x) => x.hash(state),
            PV::Int(x) => x.hash(state),
            PV::UInt(x) => x.hash(state),
            PV::Bool(x) => x.hash(state),
            PV::Nil => 0.hash(state),
            PV::Real(x) => x.to_ne_bytes().hash(state),
            PV::Char(x) => x.hash(state),
            PV::Id(x) => x.hash(state),
            #[cfg(feature = "math")]
            PV::Vec2(Vec2 { x, y }) => { x.to_ne_bytes().hash(state);
                                         y.to_ne_bytes().hash(state) },
            #[cfg(feature = "math")]
            PV::Vec3(Vec3 { x, y, z }) => { x.to_ne_bytes().hash(state);
                                            y.to_ne_bytes().hash(state);
                                            z.to_ne_bytes().hash(state) },
            PV::Ref(_) => unimplemented!("Hash is unimplemented for references"),
        }
    }
}

impl LispFmt for PV {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            PV::Nil => write!(f, "nil"),
            PV::Bool(true) => write!(f, "true"),
            PV::Bool(false) => write!(f, "false"),
            PV::Int(n) => write!(f, "{n}"),
            PV::UInt(n) => write!(f, "{n}u"),
            PV::Real(a) => write!(f, "{a}"),
            PV::Sym(id) => write!(f, "{id}"),
            PV::Char(c) => write!(f, "(char {c})"),
            PV::Id(c) => write!(f, "(id {c:?})"),
            #[cfg(feature = "math")]
            PV::Vec2(Vec2 { x, y }) => write!(f, "(vec2 {x} {y})"),
            #[cfg(feature = "math")]
            PV::Vec3(Vec3 { x, y, z }) => write!(f, "(vec3 {x} {y} {z})"),
            PV::Ref(p) => atom_fmt(p, visited, f)
        }
    }
}

impl From<PV> for bool {
    fn from(pv: PV) -> bool {
        match pv {
            PV::Bool(v) => v,
            PV::Nil => false,
            _ => true,
        }
    }
}

macro_rules! mark_gray {
    ($elem:expr, $gray:expr) => {
        if let PV::Ref(ptr) = $elem {
            (*ptr).set_color(Color::Gray);
            $gray.push(ptr);
        }
    }
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct Cons {
    pub car: PV,
    pub cdr: PV,
}

impl Cons {
    pub fn new(car: PV, cdr: PV) -> Cons {
        Cons { car, cdr }
    }
}

impl Traceable for Cons {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        unsafe {
            mark_gray!(self.car, gray);
            mark_gray!(self.cdr, gray);
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        self.car.update_ptrs(reloc);
        self.cdr.update_ptrs(reloc);
    }
}

impl LispFmt for Cons {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pv = NkAtom::make_ref(self as *const Cons as *mut Cons);
        ConsIter { item: pv }.lisp_fmt(visited, f)
    }
}

impl Traceable for HashMap<PV, PV> {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        for (k, v) in self.iter() {
            unsafe {
                mark_gray!(*k, gray);
                mark_gray!(*v, gray);
            }
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        for (k, v) in self.iter_mut() {
            let k_ptr = k as *const PV as *mut PV;
            unsafe {
                // NOTE: This should be safe, as this won't actually change the
                //       hash map key, it will just point it back to the right
                //       memory location.
                (*k_ptr).update_ptrs(reloc);
            }
            v.update_ptrs(reloc);
        }
    }
}

impl Traceable for Vec<PV> {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        for v in self.iter() {
            unsafe { mark_gray!(*v, gray) }
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        for v in self.iter_mut() {
            v.update_ptrs(reloc);
        }
    }
}

pub enum ConsElem {
    Head(PV),
    Tail(PV)
}

impl ConsElem {
    pub fn get(&self) -> PV {
        use ConsElem::*;
        match self {
            Head(x) | Tail(x) => *x
        }
    }
}

#[derive(Clone)]
pub struct ConsIter {
    item: PV
}

impl Iterator for ConsIter {
    type Item = ConsElem;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            Some(match self.item {
                PV::Nil => return None,
                PV::Ref(r) => match to_fissile_ref(r) {
                    NkRef::Cons(p) => {
                        self.item = (*p).cdr;
                        ConsElem::Head((*p).car)
                    },
                    _ => {
                        self.item = PV::Nil;
                        ConsElem::Tail(PV::Ref(r))
                    }
                },
                x => {
                    self.item = PV::Nil;
                    ConsElem::Tail(x)
                }
            })
        }
    }
}

pub enum ConsItem {
    Car(PV),
    Cdr(PV),
}

impl LispFmt for ConsItem {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let x = match self {
            ConsItem::Car(x) => { write!(f, "Car(")?; x },
            ConsItem::Cdr(x) => { write!(f, "Cdr(")?; x },
        };
        x.lisp_fmt(visited, f)?;
        write!(f, ")")
    }
}

impl ConsItem {
    pub fn any(self) -> PV {
        match self {
            ConsItem::Car(pv) => pv,
            ConsItem::Cdr(pv) => pv,
        }
    }

    pub fn car(self) -> Result<PV, Error> {
        match self {
            ConsItem::Car(pv) => Ok(pv),
            ConsItem::Cdr(_) => err!(UnexpectedDottedList,),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PVIterSrc<'a> {
    item: PV,
    nk: &'a Arena,
    src: Source,
}

impl From<PVIterSrc<'_>> for PV {
    fn from(value: PVIterSrc<'_>) -> Self {
        value.item
    }
}

impl Iterator for PVIterSrc<'_> {
    type Item = (ConsItem, Source);
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            Some(match self.item {
                PV::Nil => return None,
                PV::Ref(r) => {
                    let src = self.nk.get_tag(r).cloned().unwrap_or(self.src.clone());
                    if let NkRef::Cons(p) = to_fissile_ref(r) {
                        self.item = (*p).cdr;
                        (ConsItem::Car((*p).car), src)
                    } else {
                        self.item = PV::Nil;
                        (ConsItem::Cdr(PV::Ref(r)), src)
                    }
                }
                x => {
                    self.item = PV::Nil;
                    (ConsItem::Cdr(x), self.src.clone())
                }
            })
        }
    }
}

#[derive(Debug, Clone)]
pub struct PVIter {
    item: PV,
}

impl From<PVIter> for PV {
    fn from(value: PVIter) -> Self {
        value.item
    }
}

impl Traceable for PVIter {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        self.item.trace(gray)
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        self.item.update_ptrs(reloc)
    }
}

impl Iterator for PVIter {
    type Item = PV;
    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.item {
            PV::Nil => return None,
            PV::Ref(r) if unsafe{atom_kind(r)} == NkT::Cons => unsafe {
                let Cons { car, cdr } = *fastcast::<Cons>(r);
                self.item = cdr;
                car
            }
            x => {
                self.item = PV::Nil;
                x
            }
        })
    }
}

impl IntoIterator for PV {
    type Item = PV;
    type IntoIter = PVIter;
    fn into_iter(self) -> Self::IntoIter {
        PVIter { item: self }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Stream {
    name: String,
    id: u32,
}

impl LispFmt for Stream {
    fn lisp_fmt(&self, _: &mut VisitSet, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(stream {})", self.name)
    }
}

impl Traceable for Stream {
    fn trace(&self, _gray: &mut Vec<*mut NkAtom>) {}
    fn update_ptrs(&mut self, _reloc: &PtrMap) {}
}

#[repr(C)]
pub struct ILambda {
    pub pos: usize,
    pub args: ArgSpec,
    pub len: usize,
    pub locals: [PV],
}

pub trait SizeOf {
    fn size_of(&self) -> usize;
}

impl SizeOf for ILambda {
    fn size_of(&self) -> usize {
        let end = addr_of!(self.locals[self.len]);
        let beg = addr_of!(self.pos);
        end as usize - beg as usize
    }
}

// TODO: Should this be a DST? With locals stored inline?
#[derive(Eq, PartialEq, Debug, Clone)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct Lambda {
    pub pos: usize,
    pub locals: Vec<PV>,
    pub args: ArgSpec,
}

impl Traceable for Lambda {
    fn trace(&self, gray: &mut Vec<*mut NkAtom>) {
        for u in self.locals.iter() {
            u.trace(gray);
        }
    }

    fn update_ptrs(&mut self, reloc: &PtrMap) {
        for v in self.locals.iter_mut() {
            v.update_ptrs(reloc);
        }
    }
}

impl LispFmt for Lambda {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(λ '(")?;
        self.locals.iter().lisp_fmt(visited, f)?;
        write!(f, ") @")?;
        write!(f, "{})", self.pos)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct ExtRefID(u32);

#[derive(Debug)]
struct ExtRefMsg {
    pub id: ExtRefID,
    pub d: i8
}

/// Come and fight in the arena!
#[derive(Debug)]
pub struct Arena {
    nuke: Nuke,
    tags: FnvHashMap<*mut NkAtom, Source>,
    pub(crate) stack: Vec<PV>,
    pub(crate) symdb: SwymDb,
    pub(crate) conts: Vec<Vec<PV>>,
    pub(crate) env: Vec<PV>,
    gray: Vec<*mut NkAtom>,
    extref: FnvHashMap<ExtRefID, (i32, PV)>,
    extdrop_recv: Receiver<ExtRefMsg>,
    extdrop_send: Sender<ExtRefMsg>,
    borrows: Vec<*mut NkAtom>,
    state: GCState,
    extref_id_cnt: u32,
    no_reorder: bool,
}

// /// Serialized arena, suitable for freezing the state of a VM.
// #[derive(Debug)]
// struct ColdArena {
//     symbols: Vec<(SymID, String)>,
//     mem: Vec<NkSum>,
//     env: Vec<PV>,
// }

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum GCState {
    Mark(u32),
    Sweep,
    Sleep(i32),
}

const DEFAULT_MEMSZ: usize = 4096;
const DEFAULT_GRAYSZ: usize = 256;
const DEFAULT_STACKSZ: usize = 32;
const DEFAULT_ENVSZ: usize = 0;
// const GC_SLEEP_CYCLES: i32 = 10000;
const GC_SLEEP_MEM_BYTES: i32 = 1024 * 30;

#[derive(Debug)]
pub struct GCStats {
    pub usage: usize,
    pub size: usize,
    pub num_objects: usize,
    #[cfg(not(target_arch = "wasm32"))]
    pub time: Duration,
    pub total_allocs: usize,
    pub total_frees: usize,
}

impl Default for Arena {
    fn default() -> Self {
        Arena::new(DEFAULT_MEMSZ)
    }
}

impl Arena {
    pub fn new(memsz: usize) -> Arena {
        let (rx, tx) = channel();
        let mut ar = Arena {
            nuke: Nuke::new(memsz),
            gray: Vec::with_capacity(DEFAULT_GRAYSZ),
            stack: Vec::with_capacity(DEFAULT_STACKSZ),
            env: Vec::with_capacity(DEFAULT_ENVSZ),
            symdb: Default::default(),
            extdrop_recv: tx,
            extdrop_send: rx,
            state: GCState::Sleep(GC_SLEEP_MEM_BYTES),
            extref: FnvHashMap::default(),
            tags: FnvHashMap::default(),
            no_reorder: false,
            conts: Vec::new(),
            extref_id_cnt: 0,
            borrows: Vec::new(),
        };
        for blt in BUILTIN_SYMS.iter() {
            ar.symdb.put_static(blt);
        }
        ar
    }

    pub fn put_sym(&mut self, s: &str) -> SymRef {
        self.symdb.put_ref(s)
    }

    pub fn put_sym_id(&mut self, s: &str) -> SymID {
        self.symdb.put_ref(s).id()
    }

    pub fn print_state(&self) {
        println!("Stack: {:?}", self.stack);
        println!("Memory: {:?}", self.nuke);
    }

    pub fn minimize(&mut self) {
        self.full_collection();
        self.stack.shrink_to_fit();
        self.env.shrink_to_fit();
        self.extref.shrink_to_fit();
        self.tags.shrink_to_fit();
    }

    pub fn dup(&mut self) -> Result<(), Error> {
        if let Some(x) = self.stack.pop() {
            self.stack.push(x);
            self.stack.push(x);
            Ok(())
        } else {
            Err(ErrorKind::NotEnough { expect: 1,
                                       got: 0 }.into())
        }
    }

    #[inline]
    pub fn clz_expand(&mut self, idx: usize) -> Result<(), Error> {
        let lambda = self.stack[idx];
        with_ref!(lambda, Lambda(p) => {
            for v in (*p).locals.iter() {
                self.push(*v);
            }
            Ok(())
        })
    }

    pub fn dump_stack(&self) {
        println!("stack:");
        for (i, val) in self.stack.iter().enumerate().rev() {
            println!("  {}: {}", i, val.lisp_to_string());
        }
    }

    pub fn forbid_reordering(&mut self) {
        self.no_reorder = true
    }

    pub fn allow_reordering(&mut self) {
        self.no_reorder = false
    }

    pub fn stats(&self) -> GCStats {
        self.nuke.stats()
    }

    pub fn push_sym(&mut self, v: SymID) {
        self.stack.push(PV::Sym(v));
    }

    pub fn push_symref(&mut self, v: &SymRef) {
        self.stack.push(PV::Sym(SymID(v.inner())));
    }

    pub fn push_env(&mut self, v: PV) -> usize {
        let idx = self.env.len();
        self.env.push(v);
        idx
    }

    pub fn get_env(&self, idx: usize) -> PV {
        self.env[idx]
    }

    pub fn set_env(&mut self, idx: usize, v: PV) {
        self.env[idx] = v;
    }

    pub fn push(&mut self, v: PV) {
        self.stack.push(v);
    }

    pub fn push_spv(&mut self, v: SPV) {
        self.push(self.extref[&v.id].1);
    }

    pub fn popn(&mut self, n: usize) {
        self.stack.truncate(self.stack.len() - n);
    }

    pub fn stack_mut(&mut self) -> &mut Vec<PV> {
        &mut self.stack
    }

    pub fn list(&mut self, n: u32) {
        if n == 0 {
            self.push(PV::Nil);
            return;
        }
        self.mem_fit::<Cons>(n as usize);
        let self_ptr = self as *mut Arena;
        let top = self.stack.len();
        let idx = top - (n as usize);
        let (head, mut cell) = self.alloc::<Cons>();
        for item in self.stack[idx..top - 1].iter() {
            let (head, next) = unsafe { (*self_ptr).alloc::<Cons>() };
            unsafe {
                ptr::write(cell, Cons::new(*item, PV::Ref(head)))
            }
            cell = next;
        }
        unsafe {
            ptr::write(cell, Cons::new(self.stack[top - 1], PV::Nil))
        }
        self.stack.truncate(idx);
        self.stack.push(PV::Ref(head));
    }

    pub fn list_dot_srcs(&mut self,
                         n: u32,
                         mut srcs: impl Iterator<Item = Source>,
                         dot: bool) {
        if n == 0 {
            self.push(PV::Nil);
            return;
        }
        assert!(if dot { n >= 2 } else { true });
        self.mem_fit::<Cons>(n as usize);
        let self_ptr = self as *mut Arena;
        let top = self.stack.len();
        let idx = top - (n as usize);
        let (mut head, mut cell) = self.alloc::<Cons>();
        let orig_head = head;
        for item in self.stack[idx..top - 1 - dot as usize].iter() {
            let (nhead, next) = unsafe { (*self_ptr).alloc::<Cons>() };
            unsafe {ptr::write(cell, Cons::new(*item, PV::Ref(nhead)))}
            self.tags.insert(head, srcs.next().expect("Not enough sources for list"));
            head = nhead;
            cell = next;
        }
        unsafe {
            ptr::write(cell, Cons::new(self.stack[top - 1 - dot as usize], if dot {
                self.stack[top - 1]
            } else {
                PV::Nil
            }))
        }
        self.stack.truncate(idx);
        self.stack.push(PV::Ref(orig_head));
    }

    pub fn list_dot(&mut self,
                    n: u32,
                    dot: bool) {
        if n == 0 {
            self.push(PV::Nil);
            return;
        }
        assert!(if dot { n >= 2 } else { true });
        self.mem_fit::<Cons>(n as usize);
        let self_ptr = self as *mut Arena;
        let top = self.stack.len();
        let idx = top - (n as usize);
        let (head, mut cell) = unsafe { (*self_ptr).alloc::<Cons>() };
        let _orig_cell = cell;
        for item in self.stack[idx..top - 1 - dot as usize].iter() {
            let (head, next) = unsafe { (*self_ptr).alloc::<Cons>() };
            unsafe {ptr::write(cell, Cons::new(*item, PV::Ref(head)))}
            cell = next;
        }
        unsafe {
            ptr::write(cell, Cons::new(self.stack[top - 1 - dot as usize], if dot {
                self.stack[top - 1]
            } else {
                PV::Nil
            }))
        }
        self.stack.truncate(idx);
        self.stack.push(PV::Ref(head));
    }

    pub fn make_extref(&mut self, v: PV) -> SPV {
        let id = ExtRefID(self.extref_id_cnt);
        self.extref_id_cnt += 1;
        self.extref.insert(id, (1, v));
        SPV { id,
              ar: self.extdrop_send.clone() }
    }

    pub fn has_mut_extrefs(&self) -> bool {
        for val in self.nuke.iter() {
            if let NkRef::Object(s) = to_fissile_ref(val) {
                if unsafe{(*s).rc()} > 1 {
                    return true;
                }
            }
        }
        false
    }

    pub fn pop_spv(&mut self) -> Result<SPV, Error> {
        if let Some(res) = self.stack.pop() {
            Ok(self.make_extref(res))
        } else {
            Err(ErrorKind::NotEnough { expect: 1
                                     , got: 0 }.into())
        }
    }

    pub fn pop(&mut self) -> Result<PV, Error> {
        self.stack.pop().ok_or_else(|| ErrorKind::NotEnough {
            got: 0,
            expect: 1,
        }.into())
    }

    pub fn top(&self) -> PV {
        self.stack[self.stack.len() - 1]
    }

    pub fn from_top(&self, d: usize) -> PV {
        self.stack[self.stack.len() - d]
    }

    pub fn peek(&self) -> Result<PV, RuntimeError> {
        if self.stack.is_empty() {
            RuntimeError::err("Stack was empty.".to_string())
        } else {
            Ok(self.stack[self.stack.len() - 1])
        }
    }

    pub fn untag_ast(&mut self, v: PV) {
        let PV::Ref(p) = v else {return};
        let NkRef::Cons(cns) = to_fissile_ref(p) else {return};
        self.untag(p);
        unsafe {
            self.untag_ast((*cns).car);
            self.untag_ast((*cns).cdr);
        }
    }

    pub fn append(&mut self, n: u32) -> Result<(), Error> {
        let top = self.stack.len();
        let idx = top - (n as usize);
        let top_it = self.stack[idx + 1..top].iter();
        for (item_ref, next) in self.stack[idx..top - 1].iter().zip(top_it) {
            let mut item = *item_ref;
            item.append(*next)?;
        }
        self.stack.truncate(idx + 1);
        Ok(())
    }

    /**
     * Pop two elements off the stack and `cons` them together.
     *
     * # Safety
     * This function requires at least two values to be placed
     * on the stack before it is called. If this requirement is
     * not met the function will cause a buffer underflow read.
     */
    pub fn cons(&mut self) {
        let top = self.stack.len();
        let args = &self.stack[top - 2..];
        let mem = self.put_pv(Cons {
            car: args[0],
            cdr: args[1],
        });
        self.stack.truncate(top - 2);
        self.stack.push(mem);
    }

    #[inline]
    pub fn tag(&mut self, item: *mut NkAtom, tag: Source) {
        self.tags.insert(item, tag);
    }

    pub fn clear_tags(&mut self) {
        self.tags.clear();
    }

    pub fn get_tag(&self, item: *mut NkAtom) -> Option<&Source> {
        self.tags.get(&item)
    }

    pub fn untag(&mut self, item: *mut NkAtom) {
        self.tags.remove(&item);
    }

    fn update_ptrs(&mut self, tok: RelocateToken) {
        if self.nuke.reloc().is_empty() {
            self.nuke.confirm_relocation(tok);
            return
        }

        if self.no_reorder {
            panic!("Reordering forbidden");
        }

        let tags = self.tags.keys().copied().collect::<Vec<_>>();
        for old in tags.into_iter() {
            let new = self.nuke.reloc().get(old);
            let src = self.tags.remove(&old).unwrap();
            self.tags.insert(new as *mut NkAtom, src);
        }

        for (_id, (_, pv)) in self.extref.iter_mut() {
            pv.update_ptrs(self.nuke.reloc());
        }
        for ptr in self.gray.iter_mut() {
            *ptr = self.nuke.reloc().get(*ptr) as *mut NkAtom;
        }
        for ptr in self.borrows.iter_mut() {
            *ptr = self.nuke.reloc().get(*ptr) as *mut NkAtom;
        }
        for obj in self.nuke.iter_mut() {
            update_ptr_atom(obj, self.nuke.reloc());
        }
        for pv in self.stack.iter_mut().chain(self.env.iter_mut()) {
            pv.update_ptrs(self.nuke.reloc());
        }
        for cont in self.conts.iter_mut() {
            cont.update_ptrs(self.nuke.reloc());
        }
        self.nuke.confirm_relocation(tok);
    }

    pub fn pop_borrows(&mut self) {
        for obj in self.borrows.drain(..) {
            if let NkMut::Object(s) = to_fissile_mut(obj) {
                unsafe { (*s).void() }
            }
        }
    }

    pub fn push_borrow(&mut self, rf: *mut NkAtom) {
        self.borrows.push(rf)
    }

    fn mem_fit<T: Fissile>(&mut self, n: usize) {
        unsafe {
            if let Some(tok) = self.nuke.fit::<T>(n) {
                self.update_ptrs(tok);
            }
        }
    }

    pub fn put_pv<T>(&mut self, v: T) -> PV where T: Fissile {
        let (hp, _) = self.put(v);
        PV::Ref(hp)
    }

    pub fn put<T>(&mut self, v: T) -> (*mut NkAtom, *mut T) where T: Fissile {
        self.state = match self.state {
            GCState::Sleep(bytes) => GCState::Sleep(bytes - Nuke::size_of::<T>() as i32),
            x => x
        };
        unsafe {
            let (headp, ptr, grow) = self.nuke.alloc::<T>();
            ptr::write(ptr, v);
            if let Some(tok) = grow {
                self.update_ptrs(tok);
            }
            (headp, ptr)
        }
    }

    fn alloc<T: Fissile>(&mut self) -> (*mut NkAtom, *mut T) {
        self.state = match self.state {
            GCState::Sleep(bytes) => GCState::Sleep(bytes - Nuke::size_of::<T>() as i32),
            x => x
        };
        unsafe {
            let (headp, ptr, grow) = self.nuke.alloc::<T>();
            if let Some(tok) = grow {
                self.update_ptrs(tok);
            }
            (headp, ptr)
        }
    }

    pub fn push_new<T: Fissile>(&mut self, v: T) {
        let pv = self.put_pv(v);
        self.stack.push(pv);
    }

    #[inline]
    fn sweep_compact(&mut self) {
        let reloc = unsafe { self.nuke.sweep_compact() };
        self.update_ptrs(reloc);
        self.state = GCState::Sleep(GC_SLEEP_MEM_BYTES);
    }

    #[inline]
    fn mark_step(&mut self, steps: u32) {
        for _ in 0..steps {
            match self.gray.pop() {
                Some(obj) => mark_atom(obj, &mut self.gray),
                None => {
                    self.state = GCState::Sweep;
                    break;
                }
            }
        }
    }

    #[inline]
    fn mark_begin(&mut self) {
        self.clear_extrefs();
        self.state = GCState::Mark(1 + (self.nuke.num_atoms() / 1000) as u32);
        let it = self.stack.iter()
                           .chain(self.env.iter())
                           .chain(self.conts.iter().flatten())
                           .chain(self.extref.values().map(|(_, pv)| pv))
                           .filter_map(|obj| if let PV::Ref(cell) = *obj {
                               Some(cell)
                           } else {
                               None
                           })
                           .chain(self.borrows.iter().copied());
        for cell in it {
            unsafe {
                (*cell).set_color(Color::Gray);
                self.gray.push(cell);
            }
        }
    }

    #[inline]
    fn clear_extrefs(&mut self) {
        while let Ok(ExtRefMsg{id, d}) = self.extdrop_recv.try_recv() {
            match self.extref.entry(id) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().0 += d as i32;
                    if entry.get().0 <= 0 {
                        entry.remove();
                    }
                },
                Entry::Vacant(_) => unreachable!()
            }
        }
    }

    #[inline]
    pub fn collect(&mut self) {
        match self.state {
            GCState::Sleep(x) if x <= 0 =>
                self.mark_begin(),
            GCState::Sleep(_) => (),
            GCState::Mark(num_steps) =>
                self.mark_step(num_steps),
            GCState::Sweep => self.sweep_compact(),
        }
    }

    /// Assumes that the GC is *not* in a Sleep state.
    fn finish_cycle(&mut self) {
        while self.state != GCState::Sweep {
            self.mark_step(100);
        }
        self.sweep_compact();
    }

    /// Assumes that the GC is in a Sleep state.
    fn mark_and_sweep(&mut self) {
        self.mark_begin();
        self.finish_cycle()
    }

    /// Perform a full GC collection, this may finish a currently ongoing collection
    /// and start a new one afterwards.
    pub fn full_collection(&mut self) {
        match self.state {
            GCState::Sleep(_) => self.mark_and_sweep(),
            _ => {
                self.finish_cycle();
                self.mark_and_sweep();
            }
        }
    }

    /// Remove all allocated objects
    pub fn ignore_and_sweep(&mut self) {
        if !matches!(self.state, GCState::Sleep(_)) {
            self.finish_cycle();
        }
        self.stack.clear();
        self.env.clear();
        self.gray.clear();
        for obj in self.nuke.iter_mut() {
            unsafe {
                (*obj).set_color(Color::White);
            }
        }
        self.sweep_compact();
    }

    #[cfg(not(feature = "freeze"))]
    pub fn freeze(&self) -> i32 { unimplemented!("freeze") }

    #[cfg(feature = "freeze")]
    pub fn freeze(&self) -> i32 {
        let nk = self.nuke.shallow_clone();

        let mut out: Vec<u8> = vec![];
        let base = nk.fst() as usize;
        let mut reloc = PtrMap::default();
        unsafe {
            for obj in nk.iter() {
                let offset = obj as usize - base;
                reloc.push(obj, offset as *const NkAtom);
                match to_fissile_ref(obj) {
                    NkRef::Void(_) => unimplemented!(),
                    NkRef::Cons(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    NkRef::Intr(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    NkRef::Lambda(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    NkRef::String(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    NkRef::PV(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    NkRef::Vector(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    #[cfg(feature = "math")] NkRef::Vec4(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    #[cfg(feature = "math")] NkRef::Mat2(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    #[cfg(feature = "math")] NkRef::Mat3(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    #[cfg(feature = "math")] NkRef::Mat4(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    NkRef::Continuation(x) =>
                        bincode::serialize_into(&mut out, &*x).unwrap(),
                    s => todo!("{s:?}")
                }
                // bincode::serialize_into(out, *obj);
            }
        }

        todo!()
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        self.finish_cycle();
    }
}

/// Safe Primitive Value, a way of safely referring to GC storage
///
/// The name is based on the internal-use `spaik::raw::nkgc::PV` type,
/// which itself stands for Primitive Value. Unlike the `PV` type `SPV` makes
/// sure that the data it refers to is kept alive during garbage collection, and
/// that when data is moved during garbage collection it still refers to the
/// correct memory location.
#[derive(Debug)]
pub struct SPV {
    ar: Sender<ExtRefMsg>,
    id: ExtRefID,
}

impl SPV {
    pub(crate) fn pv(&self, ar: &Arena) -> PV {
        ar.extref[&self.id].1
    }

    pub fn to_string(&self, ar: &Arena) -> String {
        let pv = self.pv(ar);
        pv.lisp_to_string()
    }

    pub fn bt_op(&self, ar: &Arena) -> Option<Builtin> {
        self.pv(ar).bt_op()
    }

    pub fn args_vec(&self, ar: &mut Arena) -> Vec<SPV> {
        self.pv(ar).args().map(|v| ar.make_extref(v)).collect()
    }
}

impl Clone for SPV {
    fn clone(&self) -> Self {
        self.ar.send(ExtRefMsg { id: self.id, d: 1 }).unwrap();
        SPV { id: self.id,
              ar: self.ar.clone() }
    }
}

impl Drop for SPV {
    fn drop(&mut self) {
        // AFAIK sending only fails when the receiver is dropped, which only
        // happens when R8VM/Arena is dropped. And then the memory has been
        // freed anyway.
        self.ar.send(ExtRefMsg { id: self.id, d: -1 }).ok();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "derive")]
    use spaik_proc_macros::Fissile;

    #[test]
    fn spv() {
        let mut gc = Arena::new(128);
        let len: u32 = 10000;
        for i in 0..len {
            gc.push(PV::Int(i as Int));
        }
        gc.list(len);
        let _li = gc.pop_spv().unwrap();
    }

    #[cfg(feature = "derive")]
    #[test]
    fn virtual_destructors() {
        use spaik_proc_macros::export;

        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        pub struct TestObj {
            hello: Vec<u64>,
            thing: String,
        }
        #[export]
        impl TestObj {}
        let mut ar = Arena::new(1024);
        for i in 0..10 {
            let mut hello = vec![];
            for j in 1..100*i {
                hello.push(j * i);
            }
            let thing = String::from("lmao");
            let obj = Object::new(TestObj {
                hello, thing,
            });
            ar.put_pv(obj);
        }
        drop(ar);
        println!("phew");
    }
}
