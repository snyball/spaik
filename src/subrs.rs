//! Rust Subroutines for SPAIK LISP

use fnv::FnvHashMap;
use serde::de::DeserializeOwned;
use serde::{Serialize, Deserialize};

use crate::r8vm::{R8VM, ArgSpec};
use crate::nkgc::{PV, SPV, Arena, ObjRef};
use crate::error::{Error, ErrorKind};
use crate::{nuke::*, SymID, Builtin, deserialize};
use crate::fmt::{LispFmt, VisitSet};
use std::any::Any;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::{TryInto, TryFrom};
use std::fmt;
use std::io::{Read, Cursor};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::sync::{OnceLock, Mutex};

/// The `mem` parameter is necessary here, because some of the conversions
/// may need to create an SPV reference-counter
pub trait FromLisp<T>: Sized {
    #[allow(clippy::wrong_self_convention)]
    fn from_lisp(self, mem: &mut Arena) -> Result<T, Error>;
}

/// The `mem` parameter is necessary here, because some of the conversions
/// may need to do memory allocation.
pub trait IntoLisp: Sized {
    fn into_spv(self, mem: &mut Arena) -> Result<SPV, Error> {
        let pv = self.into_pv(mem)?;
        Ok(mem.make_extref(pv))
    }

    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error>;
}

pub trait RefIntoLisp {
    fn ref_into_spv(&self, mem: &mut Arena) -> Result<SPV, Error> {
        let pv = self.ref_into_pv(mem)?;
        Ok(mem.make_extref(pv))
    }

    fn ref_into_pv(&self, mem: &mut Arena) -> Result<PV, Error>;
}

impl<T> RefIntoLisp for T
    where T: IntoLisp + Clone
{
    fn ref_into_pv(&self, mem: &mut Arena) -> Result<PV, Error> {
        self.clone().into_pv(mem)
    }
}

#[allow(unused_macros)]
macro_rules! impl_objref {
    ($($from_t:ty),*) => {
        $(impl TryFrom<PV> for ObjRef<$from_t> {
            type Error = Error;
            #[inline(always)]
            fn try_from(v: PV) -> Result<ObjRef<$from_t>, Self::Error> {
                Ok(ObjRef(v.try_into()?))
            }
        })*
    };
}

macro_rules! pv_convert {
    ($pvt:ident, $($from_t:ty),*) => {
        $(impl IntoLisp for $from_t {
            fn into_pv(self, _: &mut Arena) -> Result<PV, Error> {
                Ok(PV::$pvt(self.try_into()?))
            }
        })*
        $(impl TryFrom<PV> for $from_t {
            type Error = Error;
            fn try_from(v: PV) -> Result<$from_t, Self::Error> {
                if let PV::$pvt(x) = v {
                    Ok(x.try_into()?)
                } else if let PV::Real(x) = v {
                    Ok(x as $from_t)
                } else if let PV::Int(x) = v {
                    Ok(x as $from_t)
                } else {
                    Err(Error::new(ErrorKind::TypeError {
                        expect: PV::$pvt(Default::default()).bt_type_of(),
                        got: v.bt_type_of(),
                    }))
                }
            }
        }
        impl TryFrom<PV> for ObjRef<$from_t> {
            type Error = Error;
            #[inline(always)]
            fn try_from(v: PV) -> Result<ObjRef<$from_t>, Self::Error> {
                Ok(ObjRef(v.try_into()?))
            }
        })*
    };
}

pv_convert!(Int,
            i8, u8,
            i16, u16,
            i32, u32,
            i64, u64,
            i128, u128,
            isize, usize);

pv_convert!(Real,
            f32);

#[cfg(feature = "shipyard")]
impl TryFrom<PV> for shipyard::EntityId {
    type Error = Error;

    fn try_from(value: PV) -> Result<Self, Self::Error> {
        if let PV::Id(v) = value {
            Ok(v)
        } else {
            err!(TypeError, expect: Builtin::Id, got: value.bt_type_of())
        }
    }
}

#[cfg(feature = "shipyard")]
impl_objref!(shipyard::EntityId);

#[cfg(feature = "shipyard")]
impl IntoLisp for shipyard::EntityId {
    fn into_pv(self, _mem: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Id(self))
    }
}

#[cfg(feature = "math")]
impl TryFrom<PV> for glam::Vec2 {
    type Error = Error;

    fn try_from(value: PV) -> Result<Self, Self::Error> {
        if let PV::Vec2(v) = value {
            Ok(v)
        } else {
            err!(TypeError, expect: Builtin::Vec2, got: value.bt_type_of())
        }
    }
}

#[cfg(feature = "math")]
impl TryFrom<PV> for glam::Vec3 {
    type Error = Error;

    fn try_from(value: PV) -> Result<Self, Self::Error> {
        if let PV::Vec3(v) = value {
            Ok(v)
        } else {
            err!(TypeError, expect: Builtin::Vec3, got: value.bt_type_of())
        }
    }
}

#[cfg(feature = "math")]
impl TryFrom<PV> for glam::Vec4 {
    type Error = Error;

    fn try_from(value: PV) -> Result<Self, Self::Error> {
        with_ref!(value, Vec4(v) => { Ok(*v) })
    }
}

#[cfg(feature = "math")]
impl IntoLisp for glam::Vec2 {
    fn into_pv(self, _mem: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Vec2(self))
    }
}

#[cfg(feature = "math")]
impl IntoLisp for glam::Vec3 {
    fn into_pv(self, _mem: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Vec3(self))
    }
}

#[cfg(feature = "math")]
impl IntoLisp for glam::Vec4 {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put_pv(self))
    }
}

#[cfg(feature = "math")]
impl_objref!(glam::Vec2, glam::Vec3, glam::Vec4);

impl IntoLisp for char {
    fn into_pv(self,_: &mut Arena) -> Result<PV,Error>{
        Ok(PV::Char(self))
    }

}
impl TryFrom<PV>for char {
    type Error = Error;
    fn try_from(v:PV) -> Result<char,Self::Error>{
        if let PV::Char(x) = v {
            Ok(x)
        } else {
            Err(Error::new(ErrorKind::TypeError {
                expect:PV::Char(Default::default()).bt_type_of(),got:v.bt_type_of(),
            }))
        }
    }

}
impl TryFrom<PV>for ObjRef<char>{
    type Error = Error;
    #[inline(always)]
    fn try_from(v:PV) -> Result<ObjRef<char>,Self::Error>{
        Ok(ObjRef(v.try_into()?))
    }
}

impl IntoLisp for () {
    fn into_pv(self, _: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Nil)
    }
}

impl TryFrom<PV> for () {
    type Error = Error;
    fn try_from(v: PV) -> Result<(), Self::Error> {
        if let PV::Nil = v {
            Ok(())
        } else {
            Err(Error::new(ErrorKind::TypeError {
                expect: PV::Nil.bt_type_of(),
                got: v.bt_type_of(),
            }))
        }
    }
}

/**
 * A type that all SPAIK values may be converted to.
 *
 * ```rust
 * use spaik::{Spaik, Ignore};
 * let mut vm = Spaik::new_no_core();
 * // Both of these succeed
 * let _: Ignore = vm.eval("1").unwrap();
 * let _: Ignore = vm.eval(r#"(concat "a" "b")"#).unwrap();
 * ```
 */
pub struct Ignore;

impl IntoLisp for Ignore {
    fn into_pv(self, _: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Nil)
    }
}

impl TryFrom<PV> for Ignore {
    type Error = Error;
    fn try_from(_v: PV) -> Result<Ignore, Self::Error> {
        Ok(Ignore)
    }
}

impl IntoLisp for bool {
    fn into_pv(self, _: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Bool(self))
    }
}

impl IntoLisp for &str {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put_pv(self.to_string()))
    }
}

impl IntoLisp for String {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put_pv(self))
    }
}

impl IntoLisp for SymID {
    fn into_pv(self, _mem: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Sym(self))
    }
}

impl<T> IntoLisp for Vec<T>
    where T: IntoLisp
{
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        let arr = self.into_iter()
                      .map(|v| v.into_pv(mem))
                      .collect::<Result<Vec<PV>, _>>()?;
        Ok(mem.put_pv(arr))
    }
}

impl<T> TryFrom<PV> for Vec<T>
    where T: TryFrom<PV, Error=Error>
{
    type Error = Error;
    fn try_from(v: PV) -> Result<Vec<T>, Self::Error> {
        with_ref!(v, Vector(v) => {
            (*v).iter().map(|&x| x.try_into())
                    .collect::<Result<_, _>>()
        })
    }
}

impl<K, V> TryFrom<PV> for HashMap<K, V>
    where K: std::hash::Hash + Eq + TryFrom<PV, Error=Error>,
          V: TryFrom<PV, Error=Error>
{
    type Error = Error;
    fn try_from(v: PV) -> Result<HashMap<K, V>, Self::Error> {
        with_ref!(v, Table(v) => {
            (*v).iter().map(|(&k, &v)| Ok((k.try_into()?, v.try_into()?)))
                    .collect::<Result<_, _>>()
        })
    }
}

impl<K, V> IntoLisp for HashMap<K, V>
    where K: std::hash::Hash + Eq + IntoLisp,
          V: IntoLisp
{
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        let arr = self.into_iter()
                      .map(|(k, v)| -> Result<_, Error> {
                          Ok((k.into_pv(mem)?, v.into_pv(mem)?))
                      })
                      .collect::<Result<FnvHashMap<PV, PV>, _>>()?;
        Ok(mem.put_pv(arr))
    }
}


/// NOTE: This is safe because while the `String` is shifted around by the
/// GC mark-sweep phase, the actual allocated string contents are not.
/// XXX: This definition also means that strings *must* be immutable.
impl<'a> TryFrom<PV> for &'a str {
    type Error = Error;
    fn try_from(v: PV) -> Result<&'a str, Self::Error> {
        with_ref!(v, String(s) => { Ok(&*s) })
    }
}

impl<T, E> IntoLisp for Result<T, E>
    where T: IntoLisp, E: Into<Error>
{
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        match self {
            Ok(v) => v.into_pv(mem),
            Err(e) => Err(e.into()),
        }
    }
}

pub trait CloneSubr: Subr {
    fn clone_subr(&self) -> Box<dyn Subr>;
}

impl<T> CloneSubr for T
where
    T: 'static + Subr + Clone
{
    fn clone_subr(&self) -> Box<dyn Subr> {
        Box::new(self.clone())
    }
}

#[cfg(feature = "freeze")]
pub type SubrThawFn = fn(from: &mut dyn Read) -> Result<Box<dyn Subr>, Error>;
#[cfg(feature = "freeze")]
static SUBR_THAW_FNS: OnceLock<Mutex<FnvHashMap<TypePath, SubrThawFn>>> = OnceLock::new();
#[cfg(feature = "freeze")]
static SUBRS: OnceLock<Mutex<FnvHashMap<TypePath, Box<dyn CloneSubr>>>> = OnceLock::new();

#[cfg(feature = "freeze")]
pub struct Zubr {
    name: TypePath,
    data: Option<Vec<u8>>,
}

#[cfg(feature = "freeze")]
impl Zubr {
    pub fn funmut<T: Subr + DeserializeOwned>() {
        let thaw_fns = SUBR_THAW_FNS.get_or_init(|| Mutex::new(FnvHashMap::default()));
        if let Entry::Vacant(e) = thaw_fns.lock().unwrap().entry(TypePath::of::<T>()) {
            e.insert(|from| {
                use bincode::Options;
                let opts = bincode::DefaultOptions::new();
                let obj: T = opts.deserialize_from(from).unwrap();
                Ok(obj.into_subr())
            });
        }
    }

    pub fn fun<A, R, F>(f: F)
        where A: Send + 'static,
              R: Send + 'static,
              F: Funcable<A, R> + IntoSubr<A, R> + Clone + 'static
    {
        let thaw_fns = SUBR_THAW_FNS.get_or_init(|| Mutex::new(FnvHashMap::default()));
        let subrs = SUBRS.get_or_init(|| Mutex::new(FnvHashMap::default()));
        if let Entry::Vacant(e) = thaw_fns.lock().unwrap().entry(TypePath::of::<F>()) {
            subrs.lock().unwrap().insert(TypePath::of::<F>(), Box::new(RLambda::new(f)));
            e.insert(|_| {
                let subrs = SUBRS.get_or_init(|| Mutex::new(FnvHashMap::default()));
                Ok(subrs.lock().unwrap()[&TypePath::of::<F>()].clone_subr())
            });
        }
    }

    pub fn thaw(&self) -> Result<Box<dyn Subr>, Error> {
        let thaw_fns = SUBR_THAW_FNS.get_or_init(|| Mutex::new(FnvHashMap::default()));
        // let mut cr = Cursor::new(&self.data);
        let empty = [];
        let mut cr = if let Some(ref data) = self.data {
            Cursor::new(&data[..])
        } else {
            Cursor::new(&empty[..])
        };
        (thaw_fns.lock().unwrap()[&self.name])(&mut cr)
    }
}

#[cfg(not(feature = "freeze"))]
pub unsafe trait Subr: Send + 'static {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error>;
    fn name(&self) -> &'static str;
}
#[cfg(feature = "freeze")]
pub unsafe trait Subr: Send + 'static {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error>;
    fn name(&self) -> &'static str;
    fn freeze(&self) -> Zubr {
        Zubr { name: TypePath::of::<Self>(), data: None }
    }
}

pub trait BoxSubr {
    fn into_subr(self) -> Box<dyn Subr>;
}

impl<T> BoxSubr for T where T: Subr + Sized + 'static {
    fn into_subr(self) -> Box<dyn Subr> {
        Box::new(self)
    }
}

pub trait Funcable<A, R>: Send + 'static {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error>;
}

macro_rules! impl_funcable {
    ($($x:tt),*) => {
        #[allow(non_snake_case, unused_parens)]
        impl<Funk, Rt, $($x),*> Funcable<($($x,)*), Rt> for Funk
            where Funk: FnMut($($x),*) -> Rt + Send + 'static,
                  $(PV: FromLisp<ObjRef<$x>>,)*
                  Rt: IntoLisp
        {
            fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
                let ($(ObjRef($x)),*) = match &args[..] {
                    &[$($x),*] => ($($x.from_lisp(&mut vm.mem)?),*),
                    _ => return err!(ArgError,
                                     expect: ArgSpec::normal(count_args!($($x),*)),
                                     got_num: args.len() as u32)
                };
                (self)($($x),*).into_pv(&mut vm.mem)
            }
        }

        impl<Funk, Rt, $($x),*> IntoSubr<($($x,)*), Rt> for Funk
            where Funk: FnMut($($x),*) -> Rt + Funcable<($($x,)*), Rt> + 'static,
                  $($x: Send + 'static,)*
                  Rt: Send + IntoLisp + 'static,
        {
            fn into_subr(self) -> Box<dyn Subr> {
                Box::new(RLambda::new(self))
            }
        }

        impl<Funk, Rt, $($x),*> Lispify<($($x,)*), Rt, fn()> for Funk
            where Funk: IntoSubr<($($x,)*), Rt>
        {
            fn lispify(self, mem: &mut Arena) -> Result<PV, Error> {
                self.into_subr().into_pv(mem)
            }
        }
    };
}

impl_funcable!();
impl_funcable!(A);
impl_funcable!(A, B);
impl_funcable!(A, B, C);
impl_funcable!(A, B, C, D);
impl_funcable!(A, B, C, D, E);
impl_funcable!(A, B, C, D, E, F);
impl_funcable!(A, B, C, D, E, F, G);
impl_funcable!(A, B, C, D, E, F, G, H);
impl_funcable!(A, B, C, D, E, F, G, H, I);
impl_funcable!(A, B, C, D, E, F, G, H, I, J);
impl_funcable!(A, B, C, D, E, F, G, H, I, J, K);
impl_funcable!(A, B, C, D, E, F, G, H, I, J, K, L);

#[derive(Serialize, Deserialize)]
pub struct RLambda<F, A, R>
    where A: Send + 'static, R: Send + 'static, F: Funcable<A, R>
{
    f: F,
    _phantom: PhantomData<(A, R)>,
}

impl<F, A, R> Clone for RLambda<F, A, R>
    where F: Clone, A: Send + 'static, R: Send + 'static, F: Funcable<A, R>
{
    fn clone(&self) -> Self {
        Self { f: self.f.clone(),
               _phantom: Default::default() }
    }
}

unsafe impl<F, A, R> Subr for RLambda<F, A, R>
    where A: Send, R: Send, F: Funcable<A, R> + Any
{
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
        self.f.call(vm, args)
    }

    fn name(&self) -> &'static str {
        std::any::type_name::<F>()
    }
}

impl<F, A, R> RLambda<F, A, R>
    where A: Send + 'static, R: Send + 'static, F: Funcable<A, R>
{
    pub fn new(f: F) -> Self {
        RLambda { f, _phantom: Default::default() }
    }
}

pub trait IntoSubr<A, R> {
    fn into_subr(self) -> Box<dyn Subr>;
}

pub trait Lispify<A, R, N> {
    fn lispify(self, mem: &mut Arena) -> Result<PV, Error>;
}

impl<T> IntoLisp for &mut T where T: Userdata {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        let (rf, _p) = mem.put(Object::from_ref(self));
        mem.push_borrow(rf);
        Ok(PV::Ref(rf))
    }
}

impl<T> Lispify<(), (), ()> for T where T: IntoLisp {
    fn lispify(self, mem: &mut Arena) -> Result<PV, Error> {
        self.into_pv(mem)
    }
}

impl fmt::Debug for Box<dyn Subr> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "(subr {})", self.name())
    }
}

impl LispFmt for Box<dyn Subr> {
    fn lisp_fmt(&self,
                _: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(subr {})", self.name())
    }
}

impl IntoLisp for Box<dyn Subr> {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put_pv(self))
    }
}

#[derive(Debug)]
pub struct PList<T>(pub T) where T: DeserializeOwned;

impl<T> TryFrom<PV> for PList<T> where T: DeserializeOwned {
    type Error = Error;
    fn try_from(value: PV) -> Result<Self, Self::Error> {
        Ok(PList(deserialize::from_pv(value)?))
    }
}

impl<T: DeserializeOwned> TryFrom<PV> for ObjRef<PList<T>> {
    type Error = Error;
    #[inline(always)]
    fn try_from(v: PV) -> Result<ObjRef<PList<T>>, Self::Error> {
        Ok(ObjRef(v.try_into()?))
    }
}

impl<T: DeserializeOwned> Deref for PList<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: DeserializeOwned> DerefMut for PList<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// The `mem` parameter is necessary here, because some of the conversions
/// may need to create an SPV reference-counter
pub trait FromLisp3<T, Q, C>: Sized {
    #[allow(clippy::wrong_self_convention)]
    fn from_lisp_3(self, mem: &mut Arena) -> Result<T, Error>;
}

impl<T> FromLisp3<Option<T>, Option<()>, ()> for PV where PV: FromLisp<T>, T: Sized {
    fn from_lisp_3(self, mem: &mut Arena) -> Result<Option<T>, Error> {
        match self {
            PV::Nil => Ok(None),
            x => Ok(Some(x.from_lisp(mem)?))
        }
    }
}


impl<T> FromLisp3<T, (), ()> for PV where PV: FromLisp<T>, T: Sized {
    fn from_lisp_3(self, mem: &mut Arena) -> Result<T, Error> {
        self.from_lisp(mem)
    }
}

impl<A> Lispify<(), (), Option<A>> for Option<A> where A: IntoLisp {
    fn lispify(self, mem: &mut Arena) -> Result<PV, Error> {
        match self {
            Some(x) => x.lispify(mem),
            None => Ok(PV::Nil)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Mutex};

    #[cfg(feature = "derive")]
    use spaik_proc_macros::Userdata;

    use crate::{Spaik, PList, logging};

    use serde::{Serialize, Deserialize};

    #[test]
    fn from_plist() {
        #[derive(Debug, Deserialize, Clone, Copy, PartialEq)]
        #[serde(rename_all = "kebab-case")]
        struct Lmao {
            x: i32,
            blah_blah: f32
        }

        let lmao: Arc<Mutex<Option<Lmao>>> = Arc::new(Mutex::new(None));
        let lmao_2 = lmao.clone();
        let mut vm = Spaik::new_no_core();
        vm.set("f", move |x: PList<Lmao>| { *lmao.lock().unwrap() = Some(*x) });
        vm.exec("(f '(:x 123 :blah-blah 1.2))").unwrap();
        let lock = lmao_2.lock().unwrap();
        assert_eq!(lock.clone(), Some(Lmao { x: 123, blah_blah: 1.2 }))
    }

    #[test]
    fn option_from_lisp() {
        let mut vm = Spaik::new_no_core();
        let ans: Option<i32> = vm.eval("1").unwrap();
        assert_eq!(ans, Some(1))
    }

    #[test]
    fn option_to_lisp() {
        let mut vm = Spaik::new_no_core();
        vm.exec("(define (::is-nil? w) (= w nil))").unwrap();
        let ans: Option<i32> = None;
        let ans: bool = vm.call("::is-nil?", (ans,)).unwrap();
        assert!(ans);
        vm.exec("(define (::id w) w)").unwrap();
        let ans: Option<i32> = Some(1);
        let ans: i32 = vm.call("::id", (ans,)).unwrap();
        assert_eq!(ans, 1);
        assert_eq!(ans, 1);
    }

    #[cfg(feature = "derive")]
    #[test]
    fn method_calls() {
        use spaik_proc_macros::{methods, Userdata};

        let mut vm = Spaik::new_no_core();

        #[derive(Debug, Clone, PartialEq, PartialOrd, Userdata)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        struct Lmao {}

        #[methods(())]
        impl Lmao {
            fn foo(&self, x: i32, y: i32) -> i32 {
                x + y
            }

            fn bar(&self, x: i32, y: i32, z: &str) -> String {
                format!("answer: {} ({z})", x+y)
            }

            fn baz(&self, x: f32, y: f32, z: &str) -> String {
                format!("answer: {} ({z})", x+y)
            }
        }

        vm.set("lmao", Lmao{});
        vm.defmethods::<Lmao, ()>();
        assert_eq!(vm.eval("(lmao :foo 1 2)"), Ok(3));
        assert_eq!(vm.eval(r#"(lmao :bar 8.8 8.8 "lmao")"#), Ok("answer: 16 (lmao)"));
        assert_eq!(vm.eval(r#"(lmao :baz 8 8 "lmao")"#), Ok("answer: 16 (lmao)"));
        assert_eq!(vm.eval(r#"(lmao :baz 8.8 8.8 "lmao")"#), Ok("answer: 17.6 (lmao)"));
    }

    #[cfg(feature = "math")]
    #[test]
    fn call_with_vec() {
        let mut vm = Spaik::new_no_core();
        vm.set("f", |v: glam::Vec2| { 3.0 * v });
        assert_eq!(vm.eval("(f (vec2 1 2))"), Ok(glam::vec2(3.0, 6.0)));
        vm.set("f", |v: glam::Vec3| { 3.0 * v });
        assert_eq!(vm.eval("(f (vec3 1 2 3))"), Ok(glam::vec3(3.0, 6.0, 9.0)));
        vm.set("f", |v: glam::Vec4| { 3.0 * v });
        assert_eq!(vm.eval("(f (vec4 1 2 3 4))"), Ok(glam::vec4(3.0, 6.0, 9.0, 12.0)));
    }

    #[cfg(feature = "math")]
    #[test]
    fn call_with_vec4() {
        logging::setup_logging();
        log::trace!("Making VM ...");
        let mut vm = Spaik::new_no_core();
        vm.set("f", |v: glam::Vec4| { 3.0 * v });
        assert_eq!(vm.eval("(f (vec4 1 2 3 4))"), Ok(glam::vec4(3.0, 6.0, 9.0, 12.0)));
    }
}
