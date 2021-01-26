use crate::r8vm::{ArgSpec, R8VM};
use crate::nkgc::{PV, SPV, VLambda, Traceable, Arena};
use crate::error::{Error, ErrorKind};
use crate::nk::{NkAtom, NkRelocArray};
use crate::fmt::{LispFmt, VisitSet};
use crate::sym_db::SymDB;
use std::convert::{TryInto, TryFrom};
use std::fmt;
use std::ptr;

/// The `mem` parameter is necessary here, because some of the conversions
/// may need to do memory allocation.
pub trait IntoLisp: Sized {
    fn into_spv<'a>(self, mem: &mut Arena<'a>) -> Result<SPV<'a>, Error> {
        let pv = self.into_pv(mem)?;
        Ok(mem.make_extref(pv))
    }

    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error>;
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
                    Err(Error {
                        ty: ErrorKind::TypeError {
                            expect: PV::$pvt(Default::default()).type_of(),
                            got: v.type_of(),
                            op: Default::default(),
                            argn: 0
                        },
                        src: None
                    })
                }
            }
        })*
    };
}

pv_convert!(Int,
            i8, u8,
            i16, u16,
            i32, u32,
            i64, u64,
            i128, u128);

pv_convert!(Real,
            f32);

impl IntoLisp for bool {
    fn into_pv(self, _: &mut Arena) -> Result<PV, Error> {
        Ok(PV::Bool(self))
    }
}

impl IntoLisp for String {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put(self))
    }
}

impl<T> IntoLisp for Vec<T>
    where T: IntoLisp
{
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        let arr = self.into_iter()
                      .map(|v| v.into_pv(mem))
                      .collect::<Result<Vec<PV>, _>>()?;
        Ok(mem.put(arr))
    }
}

impl<T> TryFrom<PV> for Vec<T>
    where T: TryFrom<PV, Error=Error>
{
    type Error = Error;
    fn try_from(v: PV) -> Result<Vec<T>, Self::Error> {
        with_ref!(v, Vector(v) => {
            v.iter().map(|&x| x.try_into())
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
        with_ref!(v, String(s) => { Ok(&s) })
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

/**
 * SAFETY: The call method may be passed an arg reference into the,
 *         vm stack (which it gets a mutable reference to.) The call
 *         method may not access `args` after mutating `vm`.
 *
 *         This invariant is ensured by the lispy proc-macro, which you
 *         should use instead of implementing Subr yourself.
 */
pub unsafe trait Subr: CloneSubr {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error>;

    fn name(&self) -> &'static str;
}

impl fmt::Debug for Box<dyn Subr> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "(subr {})", self.name())
    }
}

impl LispFmt for Box<dyn Subr> {
    fn lisp_fmt(&self,
                _: &dyn SymDB,
                _: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(subr {})", self.name())
    }
}

impl Traceable for Box<dyn Subr> {
    fn trace(&self, _gray: &mut Vec<*mut NkAtom>) {}

    fn update_ptrs(&mut self, _reloc: &NkRelocArray) {}
}

pub trait CloneSubr {
    fn clone_subr(&self) -> Box<dyn Subr>;
}

impl<T> CloneSubr for T
    where T: Subr + Clone + 'static
{
    fn clone_subr(&self) -> Box<dyn Subr> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn Subr> {
    fn clone(&self) -> Box<dyn Subr> {
        self.clone_subr()
    }
}

impl IntoLisp for Box<dyn Subr> {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        let p = mem.alloc::<Self>();
        unsafe { ptr::write(p, self) }
        Ok(NkAtom::make_ref(p))
    }
}

#[inline]
fn my_function(x: i32, y: i32) -> i32 {
    println!("Inside my_function: {} {}", x, y);
    let res = x + y.pow(2);
    println!("res: {}", res);
    res
}

#[allow(non_camel_case_types)]
#[derive(Clone)]
pub struct my_function_obj {}

impl my_function_obj {
    #[inline]
    pub fn new() -> Box<dyn Subr> {
        Box::new(my_function_obj {})
    }
}

unsafe impl Subr for my_function_obj {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
        static SPEC: ArgSpec = ArgSpec::normal(2);
        SPEC.check(Default::default(), args.len() as u16)?;
        let x = args[0].try_into().map_err(|e: Error| e.argn(0))?;
        let y = args[1].try_into().map_err(|e: Error| e.argn(1))?;
        my_function(x, y).into_pv(&mut vm.mem)
    }

    fn name(&self) -> &'static str { "my-function" }
}

unsafe impl Subr for VLambda {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
        // FIXME: This works fine for lambdas that don't have an environment,
        // but will cause errors for those that do.
        // You should first fix the FIXME in r8vm for CLZCALL, extract the
        // actual calling-routine to a new R8VM method, then you can re-use that
        // here.
        if self.args.has_env() {
            unimplemented!("Calling closures as Subr is not implemented.")
        }
        vm.raw_call(self.name, args)
    }

    fn name(&self) -> &'static str {
        "lambda"
    }
}
