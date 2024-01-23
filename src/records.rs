use std::any::{Any, TypeId};

use spaik_proc_macros::Record;

use crate::error::OpName;
use crate::nuke::Object;
use crate::{Subr, swym::SymRef, nkgc::PV, r8vm::R8VM};
use crate::{Result, Fissile, Userdata, Error, FromLisp, nuke};

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
    fn field_access(&mut self, args: &[PV]) -> crate::Result<Option<PV>> {
        Ok(None)
    }
}

pub trait MethodCall {
    fn call_method(&mut self, args: &[PV]) -> crate::Result<Option<PV>> {
        Ok(None)
    }
}

unsafe impl<T> Subr for T where T: FieldAccess + MethodCall + Send + 'static {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> std::result::Result<PV, Error> {
        todo!()
    }

    fn name(&self) -> &'static str {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Spaik, Gc};

    use super::*;

    #[test]
    fn record_macro_output() {
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
        let mut x: Gc<Example> = vm.eval("g").unwrap();
        let x = x.with(|x| x.clone());
        let y: Example = vm.eval("g").unwrap();
        assert!(vm.eval::<bool>("(void? g)").unwrap());
        assert_eq!(x, Example { x: 1.0, y: 2.0, z: "z".to_string() });
        assert_eq!(y, x);
    }
}
