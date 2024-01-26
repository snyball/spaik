use spaik_proc_macros::{Record, Enum};

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

#[derive(Debug, Clone, Enum, Fissile, PartialEq)]
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
    Foo {
        x: i32,
    },
    Bar(i32, i32),
    Zed,
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

pub trait Record: Userdata + Subr {
    fn record_macro() -> Option<impl Subr>;
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
    fn struct_as_enum() {
        #[derive(Debug, Fissile, Enum, Clone, PartialEq, Eq)]
        #[cfg_attr(feature = "freeze", derive(serde::Serialize, serde::Deserialize))]
        pub struct Test1 {
            x: i32
        }
        #[derive(Debug, Fissile, Enum, Clone, PartialEq, Eq)]
        #[cfg_attr(feature = "freeze", derive(serde::Serialize, serde::Deserialize))]
        pub struct Test2;
        #[derive(Debug, Fissile, Enum, Clone, PartialEq, Eq)]
        #[cfg_attr(feature = "freeze", derive(serde::Serialize, serde::Deserialize))]
        pub struct Test3(i32, i32);
        let mut vm = Spaik::new_no_core();
        vm.enum_record::<Test1>();
        vm.exec(r##"(define g (test1 :x 2))"##).unwrap();
        vm.exec(r##"(define g2 (test2))"##).unwrap();
        vm.exec(r##"(define g3 (test3 1 2))"##).unwrap();
        let mut g: Gc<Test1> = vm.get("g").unwrap();
        assert_eq!(g.with(|t| t.clone()), Test1 { x: 2 });
        let mut g2: Gc<Test2> = vm.get("g2").unwrap();
        assert_eq!(g2.with(|t| t.clone()), Test2);
        let mut g3: Gc<Test3> = vm.get("g3").unwrap();
        assert_eq!(g3.with(|t| t.clone()), Test3(1, 2));
    }

    #[test]
    fn enum_macros() {
        let mut vm = Spaik::new_no_core();
        vm.enum_record::<EnumExample>();
        vm.record::<Example>();
        vm.exec(r##"(define g (enum-example/ayy :x 1 :y 2 :z "z"))"##).unwrap();
        vm.exec(r##"(define z (enum-example/lmao :example (example :x 1 :y 2 :z "z")))"##).unwrap();
        vm.exec(r##"(define zed (enum-example/zed))"##).unwrap();
        vm.exec(r##"(define bar (enum-example/bar 1 2))"##).unwrap();
        let mut g: Gc<EnumExample> = vm.get("g").unwrap();
        let mut z: Gc<EnumExample> = vm.get("z").unwrap();
        let mut zed: Gc<EnumExample> = vm.get("zed").unwrap();
        let mut bar: Gc<EnumExample> = vm.get("bar").unwrap();
        assert_eq!(g.with(|t| t.clone()),
                   EnumExample::Ayy { x: 1.0, y: 2.0, z: "z".to_string() });
        assert_eq!(z.with(|t| t.clone()),
                   EnumExample::Lmao { example: Example { x: 1.0, y: 2.0, z: "z".to_string() } });
        assert_eq!(zed.with(|t| t.clone()), EnumExample::Zed);
        assert_eq!(bar.with(|t| t.clone()), EnumExample::Bar(1, 2));
    }
}
