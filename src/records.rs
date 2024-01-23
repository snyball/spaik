use crate::{Subr, swym::SymRef, nkgc::PV, r8vm::R8VM, AsSym};
use crate::Result;

struct Example {
    x: f32,
    y: f32,
    z: String
}

pub trait Record {
    fn record() -> impl Subr;
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

impl Record for Example {
    fn record() -> impl Subr {
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
                let name = self.make_fn.get_or_insert_with(|| vm.sym("make-example"));
                let mut out: [Option<PV>; 3] = [None, None, None];
                into_init(vm, "example", name, args, &self.keys[..], &mut out)
            }

            fn name(&self) -> &'static str {
                "sys/example/macro-subr"
            }
        }
        Construct::default()
    }
}
