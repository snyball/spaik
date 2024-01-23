use crate::_deps::Object;
use crate::error::OpName;
use crate::r8vm::ArgSpec;
use crate::{Subr, swym::SymRef, nkgc::PV, r8vm::R8VM};
use crate::{Result, Fissile, Userdata, Error};

#[derive(Debug, Fissile)]
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
fn into_init(vm: &mut R8VM,
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
        Ok(Some(PV::Nil))
    }
}

pub trait Methods {
    fn call_method(&mut self, args: &[PV]) -> crate::Result<Option<PV>> {
        Ok(Some(PV::Nil))
    }
}

unsafe impl<T> Subr for T where T: FieldAccess + Methods + Send + 'static {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> std::result::Result<PV, Error> {
        todo!()
    }

    fn name(&self) -> &'static str {
        todo!()
    }
}

impl FieldAccess for Example {}
impl Methods for Example {}

impl Record for Example {
    fn record_macro() -> impl Subr {
        #[derive(Default)]
        struct Construct {
            keys: Vec<SymRef>,
            make_fn: Option<SymRef>,
        }
        unsafe impl Subr for Construct {
            fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> crate::Result<PV> {
                if self.keys.is_empty() {
                    self.keys = (&[":x", ":y", ":z"]).into_iter().map(|key| {
                        vm.sym(key)
                    }).collect();
                }
                let name = self.make_fn.get_or_insert_with(|| vm.sym("<ζ>::make-example"));
                let mut out: [Option<PV>; 3] = [None, None, None];
                into_init(vm, "example", name, args, &self.keys[..], &mut out)
            }

            fn name(&self) -> &'static str {
                "<ξζ>::example"
            }
        }
        Construct::default()
    }

    fn record_constructor() -> impl Subr {
        struct Construct;
        unsafe impl Subr for Construct {
            fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> crate::Result<PV> {
                ArgSpec::normal(3).check(args.len() as u16)?;
                let common_err = |e: Error| e.sop("example");
                let make_obj = || Ok(Object::new(Example {
                    x: args[0].try_into()
                              .map_err(|e: Error| e.arg_name(OpName::OpStr("x")))?,
                    y: args[1].try_into()
                              .map_err(|e: Error| e.arg_name(OpName::OpStr("y")))?,
                    z: args[2].try_into()
                              .map_err(|e: Error| e.arg_name(OpName::OpStr("z")))?,
                }));
                Ok(vm.mem.put_pv(make_obj().map_err(common_err)?))
            }

            fn name(&self) -> &'static str {
                "<ζ>::make-example"
            }
        }
        Construct
    }
}

#[cfg(test)]
mod tests {
    use crate::Spaik;

    use super::*;

    #[test]
    fn record_macro_output() {
        let mut vm = Spaik::new_no_core();
        let bx: Box<dyn Subr> = Box::new(Example::record_macro());
        vm.set("m", bx);
        assert_eq!(true,
                   vm.eval(
                       "(eq? (m :x '(1 2 3) :y 2 :z 3) '(make-example (1 2 3) 2 3))"
                   ).unwrap());
        vm.exec("(define (mm &body b) (apply m b))").unwrap();
        vm.exec("(set-macro! q mm)").unwrap();
        vm.exec("(q :x 1 :y 2 :z 3)").unwrap();
    }
}
