use spaik_proc_macros::Record;

use crate::error::OpName;

use crate::nkgc::Traceable;
use crate::{Subr, swym::SymRef, nkgc::PV, r8vm::R8VM};
use crate::{Result, Fissile, Userdata, Error};

#[derive(Debug, Record, Fissile, Clone, PartialEq)]
#[cfg_attr(feature = "freeze", derive(serde::Serialize, serde::Deserialize))]
struct Example {
    x: f32,
    y: f32,
    z: String
}

#[derive(Debug, Clone, Fissile, PartialEq)]
#[cfg_attr(feature = "freeze", derive(serde::Serialize, serde::Deserialize))]
enum EnumExample {
    Ayy {
        x: f32,
        y: f32,
        z: String
    },
    Lmao {
        example: Example
    },
}

pub struct MacroNew {
    name: &'static str,
    variant: &'static str,
    variant_maker: &'static str,
    key_strings: &'static [&'static str],
    defaults: Vec<Option<PV>>,
    keys: Vec<SymRef>,
    make_fn: Option<SymRef>,
}

unsafe impl Send for MacroNew {}

impl TryFrom<PV> for MacroNew {
    type Error = crate::Error;

    fn try_from(_: PV) -> std::result::Result<Self, Self::Error> {
        err!(ImmovableObject, name: OpName::OpStr("EnumMacro"))
    }
}

impl Traceable for MacroNew {
    fn trace(&self, gray: &mut Vec<*mut crate::_deps::NkAtom>) {
        for df in self.defaults.iter() {
            df.map(|df| df.trace(gray));
        }
    }

    fn update_ptrs(&mut self, reloc: &crate::_deps::PtrMap) {
        for df in self.defaults.iter() {
            df.map(|mut df| df.update_ptrs(reloc));
        }
    }
}

unsafe impl Subr for MacroNew {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> std::result::Result<PV, Error> {
        if self.keys.is_empty() {
            self.keys = self.key_strings.into_iter().map(|key| {
                vm.sym(key)
            }).collect();
        }
        let name = self.make_fn.get_or_insert_with(|| vm.sym(self.variant_maker));
        let mut out = self.defaults.clone();
        into_init(vm, self.name, name, args, &self.keys[..], &mut out[..])
    }

    fn name(&self) -> &'static str {
        self.variant
    }
}

pub trait Enum {
    fn enum_macros() -> impl Iterator<Item = MacroNew>;
    fn enum_constructors() -> impl Iterator<Item = Box<dyn Subr>>;
}

pub struct MacroNewVariant {
    variant: &'static str,
    variant_maker: &'static str,
    key_strings: &'static [&'static str],
}

#[inline(never)]
pub fn into_macro_news(parts: &'static [MacroNewVariant]) -> impl Iterator<Item = MacroNew> {
    parts.iter().map(|MacroNewVariant { variant, variant_maker, key_strings }:
                     &MacroNewVariant| MacroNew {
        name: "enum-example",
        variant,
        variant_maker,
        key_strings,
        defaults: vec![None; key_strings.len()],
        keys: Default::default(),
        make_fn: None,
    })
}

impl KebabTypeName for EnumExample {
    fn kebab_type_name() -> &'static str {
        "enum-example"
    }
}

impl MethodCall for EnumExample {}

impl FieldAccess for EnumExample {}

impl Enum for EnumExample {
    fn enum_macros() -> impl Iterator<Item = MacroNew> {
        const VARIANTS: [MacroNewVariant; 2] = [
            MacroNewVariant { variant: "enum-example/ayy",
                              variant_maker: "<ζ>::make-enum-example/ayy",
                              key_strings: &[":x", ":y", ":z"] },
            MacroNewVariant { variant: "enum-example/lmao",
                              variant_maker: "<ζ>::make-enum-example/lmao",
                              key_strings: &[":example"] },
        ];
        into_macro_news(&VARIANTS)
    }

    fn enum_constructors() -> impl Iterator<Item = Box<dyn Subr>> {
        use crate::_deps::*;
        struct MakeAyy;
        struct MakeLmao;
        unsafe impl Subr for MakeAyy {
            fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
                ArgSpec::normal(3).check(args.len().try_into()?)?;
                let common_err = |e: Error| e.sop("enum-example/ayy");
                let make_obj = || Ok(Object::new(EnumExample::Ayy {
                    x: args[0].try_into().map_err(|e: Error| e.arg_name(OpName::OpStr("x")))?,
                    y: args[1].try_into().map_err(|e: Error| e.arg_name(OpName::OpStr("y")))?,
                    z: args[2].try_into().map_err(|e: Error| e.arg_name(OpName::OpStr("z")))?,
                }));
                Ok(vm.mem.put_pv(make_obj().map_err(common_err)?))
            }

            fn name(&self) -> &'static str {
                "<ζ>::make-enum-example/ayy"
            }
        }
        unsafe impl Subr for MakeLmao {
            fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
                ArgSpec::normal(1).check(args.len().try_into()?)?;
                let common_err = |e: Error| e.sop("enum-example/lmao");
                let make_obj = || Ok(Object::new(EnumExample::Lmao {
                    example: args[0].try_into().map_err(|e: Error| e.arg_name(OpName::OpStr("example")))?,
                }));
                Ok(vm.mem.put_pv(make_obj().map_err(common_err)?))
            }

            fn name(&self) -> &'static str {
                "<ζ>::make-enum-example/lmao"
            }
        }
        let boxes: [Box<dyn Subr>; 2] = [Box::new(MakeAyy), Box::new(MakeLmao)];
        boxes.into_iter()
    }
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
        match *pair {
            [k, v] => for (i, key) in keys.iter().enumerate() {
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
            [_] => return err!(UnclosedDelimiter, open: ":key"),
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
    use crate::{Spaik, Gc, nuke};

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

    #[test]
    fn enum_macros() {
        let mut vm = Spaik::new_no_core();
        vm.enum_record::<EnumExample>();
        vm.exec(r##"(define g (enum-example/ayy :x 1 :y 2 :z "z"))"##).unwrap();
        let mut thing: Gc<EnumExample> = vm.get("g").unwrap();
        assert_eq!(thing.with(|t| t.clone()),
                   EnumExample::Ayy { x: 1.0, y: 2.0, z: "z".to_string() })
    }
}
