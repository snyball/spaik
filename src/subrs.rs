//! Rust Subroutines for SPAIK LISP

use crate::r8vm::R8VM;
use crate::nkgc::{PV, SPV, Traceable, Arena, ObjRef};
use crate::error::{Error, ErrorKind};
use crate::{nuke::*, SymID};
use crate::fmt::{LispFmt, VisitSet};
use crate::sym_db::SymDB;
use std::convert::{TryInto, TryFrom};
use std::fmt;
use std::ptr;

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
                    Err(Error {
                        ty: ErrorKind::TypeError {
                            expect: PV::$pvt(Default::default()).type_of(),
                            got: v.type_of(),
                        },
                        meta: Default::default(),
                    })
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
            Err(Error {
                ty: ErrorKind::TypeError {
                    expect: PV::Nil.type_of(),
                    got: v.type_of(),
                },
                meta: Default::default(),
            })
        }
    }
}

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
        Ok(mem.put(self.to_string()))
    }
}

impl IntoLisp for String {
    fn into_pv(self, mem: &mut Arena) -> Result<PV, Error> {
        Ok(mem.put(self))
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
        Ok(mem.put(arr))
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

/**
 * SAFETY: The call method may be passed an arg reference into the,
 *         vm stack (which it gets a mutable reference to.) The call
 *         method may not access `args` after mutating `vm`.
 *         -
 *         This invariant is ensured by the lispy proc-macro, which you
 *         should use instead of implementing Subr yourself.
*/
pub unsafe trait Subr: CloneSubr + Send + 'static {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error>;

    fn name(&self) -> &'static str;
}

pub trait IntoSubr: Subr {
    fn into_subr(self) -> Box<dyn Subr>;
}

impl<T> IntoSubr for T where T: Subr + Sized + 'static {
    fn into_subr(self) -> Box<dyn Subr> {
        Box::new(self)
    }
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

    fn update_ptrs(&mut self, _reloc: &PtrMap) {}
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
