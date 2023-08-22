//! Rust Subroutines for SPAIK LISP

use fnv::FnvHashMap;
use owo_colors::colors::xterm::Sundown;
use serde::de::DeserializeOwned;
use serde::{Serialize, Deserialize};

use crate::r8vm::{R8VM, ArgSpec};
use crate::nkgc::{PV, SPV, Arena, ObjRef};
use crate::error::{Error, ErrorKind};
use crate::{nuke::*, SymID};
use crate::fmt::{LispFmt, VisitSet};
use std::any::Any;
use std::collections::hash_map::Entry;
use std::convert::{TryInto, TryFrom};
use std::fmt;
use std::io::{Read, Cursor};
use std::marker::PhantomData;
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

pv_convert!(Char,
            char);

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

/**
 * SAFETY: The call method may be passed an arg reference into the,
 *         vm stack (which it gets a mutable reference to.) The call
 *         method may not access `args` after mutating `vm`.
 *         -
 *         This invariant is ensured by the lispy proc-macro, which you
 *         should use instead of implementing Subr yourself.
*/
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

impl<T> IntoLisp for &mut T where T: Userdata + Subr {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        let p = mem.put(Object::from_ref(self));
        let rf = NkAtom::make_raw_ref(p);
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
        let p = mem.put(self);
        Ok(NkAtom::make_ref(p))
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "derive")]
    use spaik_proc_macros::{Fissile, spaik_export};

    use crate::Spaik;

    use serde::{Serialize, Deserialize};

    #[cfg(feature = "derive")]
    #[test]
    fn method_calls() {
        let mut vm = Spaik::new_no_core();

        #[derive(Debug, Clone, PartialEq, PartialOrd, Fissile)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        struct Lmao {}

        #[spaik_export]
        impl Lmao {
            fn foo(&self, x: i32, y: i32) -> i32 {
                x + y
            }

            fn bar(&self, x: i32, y: i32) -> i32 {
                x + y
            }

            fn baz(&self, x: i32, y: i32, z: &str) -> String {
                format!("answer: {} ({z})", x+y)
            }
        }

        vm.set("lmao", Lmao{});
        assert_eq!(vm.eval("(lmao :foo 1 2)"), Ok(3));
        assert_eq!(vm.eval(r#"(lmao :baz 8 8 "lmao")"#), Ok("answer: 16 (lmao)"));
    }
}
