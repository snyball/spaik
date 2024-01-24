

use spaik_proc_macros::Record;

use crate::error::OpName;

use crate::{Subr, swym::SymRef, nkgc::PV, r8vm::R8VM};
use crate::{Result, Fissile, Userdata, Error};

#[derive(Debug, Record, Fissile, Clone, PartialEq)]
#[cfg_attr(feature = "freeze", derive(serde::Serialize, serde::Deserialize))]
struct Example {
    x: f32,
    y: f32,
    z: String
}

pub trait Record: Userdata + Subr {
    fn record_macro() -> impl Subr;
    fn record_constructor() -> impl Subr;
}

#[inline(never)]
pub fn into_init(vm: &mut R8VM,
                 name: &'static str,
                 make_fn: &SymRef,
                 args: &[PV],
                 keys: &[SymRef],
                 out: &mut [Option<PV>]) -> Result<PV>
{
    'outer: for pair in args.chunks(2) {
        match pair {
            &[k, v] => for (i, key) in keys.iter().enumerate() {
                if key.eq_pv(k) {
                    if out[i].is_some() {
                        return err!(DuplicateField, record: name.to_string(),
                                    field: k.to_string())
                    }
                    out[i] = Some(v);
                    continue 'outer;
                }
            }
            // FIXME: Better error message
            &[_] => return err!(UnclosedDelimiter, open: ":key"),
            _ => unreachable!(),
        }
        return err!(NoSuchField, record: name.to_string(), field: pair[0].to_string())
    }
    vm.mem.push_symref(make_fn);
    for pv in out.iter() {
        if let Some(pv) = pv {
            vm.mem.push(*pv);
        } else {
            // FIXME: List the missing fields
            return err!(RecordMissingFields,
                        record: name.to_string(),
                        fields: vec![])
        }
    }
    vm.mem.list((out.len() + 1) as u32);
    vm.mem.pop()
}

pub trait FieldAccess {
    fn field_access(&mut self, _args: &[PV]) -> crate::Result<Option<PV>> {
        Ok(None)
    }
}

pub trait MethodCall {
    fn call_method(&mut self, _args: &[PV]) -> crate::Result<Option<PV>> {
        Ok(None)
    }
}

pub trait KebabTypeName {
    fn kebab_type_name() -> &'static str;
}

unsafe impl<T> Subr for T where T: FieldAccess + MethodCall + Send + KebabTypeName + 'static {
    fn call(&mut self, _vm: &mut R8VM, _args: &[PV]) -> std::result::Result<PV, Error> {
        todo!()
    }

    fn name(&self) -> &'static str {
        Self::kebab_type_name()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Spaik, Gc};

    use super::*;

    #[test]
    fn record_macro_manual() {
        let mut vm = Spaik::new_no_core();
        let macro_bx: Box<dyn Subr> = Box::new(Example::record_macro());
        vm.set("m", macro_bx);
        let make_bx: Box<dyn Subr> = Box::new(Example::record_constructor());
        vm.set(make_bx.name(), make_bx);
        assert!(vm.eval::<bool>(
            "(eq? (m :x '(1 2 3) :y 2 :z 3) '(<ζ>::make-example (1 2 3) 2 3))"
        ).unwrap());
        vm.exec("(define (mm &body b) (apply m b))").unwrap();
        vm.exec("(set-macro! q mm)").unwrap();
        vm.exec(r##"(define g (q :x 1 :y 2 :z "z"))"##).unwrap();
        let mut gx: Gc<Example> = vm.eval("g").unwrap();
        let x = gx.with(|x| x.clone());
        drop(gx);
        let y: Example = vm.eval("g").unwrap();
        assert!(vm.eval::<bool>("(void? g)").unwrap());
        assert_eq!(x, Example { x: 1.0, y: 2.0, z: "z".to_string() });
        assert_eq!(y, x);
    }

    #[test]
    fn record_macro_auto() {
        let mut vm = Spaik::new_no_core();
        vm.record::<Example>();
        vm.exec(r##"(define g (example :x 1 :y 2 :z "z"))"##).unwrap();
        let mut gx: Gc<Example> = vm.eval("g").unwrap();
        let x = gx.with(|x| x.clone());
        drop(gx);
        let y: Example = vm.eval("g").unwrap();
        assert!(vm.eval::<bool>("(void? g)").unwrap());
        assert_eq!(y, Example { x: 1.0, y: 2.0, z: "z".to_string() });
        assert_eq!(y, x);
    }

    #[test]
    fn record_macro_auto_shared_ref() {
        let mut vm = Spaik::new_no_core();
        vm.record::<Example>();
        vm.exec(r##"(define g (example :x 1 :y 2 :z "z"))"##).unwrap();
        let _gx: Gc<Example> = vm.eval("g").unwrap();
        assert!(matches!(vm.eval::<Example>("g").map_err(|e| e.kind().clone()),
                         Err(crate::error::ErrorKind::CannotMoveSharedReference { nref: 2, .. }))) ;
    }
}
