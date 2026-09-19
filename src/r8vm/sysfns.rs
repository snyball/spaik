#![allow(non_camel_case_types)]

use std::{fmt::Write, borrow::Cow, io::BufWriter, fs, any::TypeId, hash::Hash, collections::hash_map::DefaultHasher, cmp::Ordering};

use crate::nuke::{to_fissile_ref, NkRef, NkAtom};
use crate::r8vm::VmDebugOpts;
use crate::utils::{HMap, HSet};

use crate::{subrs::{Subr, IntoLisp}, nkgc::{PV, Cons}, error::{Error, ErrorKind, Result}, fmt::{LispFmt, FmtWrap}, builtins::Builtin, utils::Success, nuke::{cast_mut, Void, Voided, Locked}, r8vm::merge_sort};
use super::{R8VM, tostring, ArgSpec, sysrand_impl};

fn join_str<IT, S>(args: IT, sep: S) -> String
where IT: Iterator<Item = PV>, S: AsRef<str>
{
    let mut out = String::new();
    let mut had_out = false;
    for val in args {
        if had_out {
            out.push_str(sep.as_ref());
        } else {
            had_out = true;
        }
        with_ref!(val, String(s) => {
            write!(&mut out, "{}", &*s).unwrap();
            Ok(())
        }).or_else(|_| -> Success {
            match val {
                PV::Char(c) => write!(&mut out, "{c}").unwrap(),
                _ => write!(&mut out, "{}", FmtWrap { val: &val }).unwrap(),
            }
            Ok(())
        }).unwrap();
    }
    out
}

macro_rules! featurefn {
    ($ft:expr, $e:expr) => {{
        #[allow(unused_mut)]
        #[cfg(feature = $ft)]
        let mut funk = || -> Result<_> {
            $e
        };
        #[cfg(not(feature = $ft))]
        let funk = || -> Result<_> {
            err!(MissingFeature, flag: $ft)
        };
        funk()
    }};
}

macro_rules! subr {
    (fn $name:ident[$name_s:expr](&mut $self:ident, $vm:ident : &mut R8VM, $args:ident : &[PV])
                    -> Result<PV> $body:block) => {
        #[derive(Clone, Copy, Debug)]
        pub struct $name;

        #[allow(unused_variables)]
        unsafe impl Subr for $name {
            fn call(&mut $self, $vm: &mut R8VM, $args: &[PV]) -> Result<PV> $body
            fn name(&self) -> &'static str { spaik_proc_macros::kebabify_plus!($name) }
        }
    };

    (fn $name:ident(&mut $self:ident, $vm:ident : &mut R8VM, $args:ident : &[PV])
                    -> Result<PV> $body:block) => {
        subr!(fn $name[stringify!($name)](&mut $self, $vm : &mut R8VM, $args : &[PV])
                                          -> Result<PV> $body);
    };

    (fn $name:ident(&mut $self:ident, $vm:ident : &mut R8VM, args: ($($arg:ident),*)) -> Result<PV> $body:block) => {
        subr!(fn $name(&mut $self, $vm: &mut R8VM, args: &[PV]) -> Result<PV> {
            subr_args!(($($arg),*) $self $vm args {
                $body
            })
        });
    };
}

macro_rules! subr_args {
    (($($arg:ident),*) $self:ident $vm:ident $args:ident $body:block) => {
        match &$args[..] {
            [$($arg),*] => {
                $body
            },
            _ => Err(error!(ArgError,
                            expect: ArgSpec::normal(count_args!($($arg),*)),
                            got_num: $args.len() as u32)
                     .op($vm.sym($self.name())))
        }
    };
}

macro_rules! std_subrs {
    ($(fn $name:ident($($inner:tt)*) -> Result<PV> $body:block)*) => {
        $(subr!(fn $name($($inner)*) -> Result<PV> $body);)*
    };
}

std_subrs! {
    fn println(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        let s = tostring(*x);
        vm.println(&s)?;
        Ok(*x)
    }

    fn clone(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.deep_clone(&mut vm.mem)
    }

    fn copy(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        unsafe {
            let mut pv = *x;
            Ok(vm.mem.copy_value(&mut pv))
        }
    }

    fn freeze(&mut self, vm: &mut R8VM, args: (_dst)) -> Result<PV> {
        featurefn!("modules", {
            let module = vm.freeze();
            let file = std::fs::File::create(_dst.str().as_ref())?;
            let mut wr = std::io::BufWriter::new(file);
            bincode::serialize_into(&mut wr, &module).unwrap();
            Ok(())
        })?;
        Ok(PV::Nil)
    }

    fn print(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        let s = tostring(*x);
        vm.print(&s)?;
        Ok(*x)
    }

    fn repr(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.lisp_to_string()
        .into_pv(&mut vm.mem)
    }

    fn dbg_repr(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        Ok(vm.mem.put_pv(format!("{x:?}")))
    }

    fn string(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        let s = match x {
            PV::Ref(y) => match to_fissile_ref(*y) {
                NkRef::String(s) => return Ok(*x),
                _ => x.lisp_to_string(),
            },
            PV::Char(c) => format!("{c}"),
            _ => x.lisp_to_string(),
        };
        s.into_pv(&mut vm.mem)
    }

    fn eval(&mut self, vm: &mut R8VM, args: (ast)) -> Result<PV> {
        vm.eval_pv(*ast)
    }

    fn read(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        vm.read(&tostring(*x))
    }

    fn read_from(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        vm.read_from(&tostring(*x))
    }

    fn vec2(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
        featurefn!("math", {
            let e = || Err(error!(ArgTypeError,
                expect: vec![Builtin::Number, Builtin::Number],
                got: vec![x.bt_type_of(), y.bt_type_of()])
                .bop(Builtin::Vec2));
            let Ok(x) = x.real() else { return e() };
            let Ok(y) = y.real() else { return e() };
            Ok(PV::Vec2(glam::vec2(x, y)))
        })
    }

    fn vec3(&mut self, vm: &mut R8VM, args: (x, y, z)) -> Result<PV> {
        featurefn!("math", {
            let e = || Err(error!(ArgTypeError,
                expect: vec![Builtin::Number,
                    Builtin::Number,
                    Builtin::Number],
                got: vec![x.bt_type_of(),
                    y.bt_type_of(),
                    z.bt_type_of()])
                .bop(Builtin::Vec3));
            let Ok(x) = x.real() else { return e() };
            let Ok(y) = y.real() else { return e() };
            let Ok(z) = z.real() else { return e() };
            Ok(PV::Vec3(glam::vec3(x, y, z)))
        })
    }

    fn vec4(&mut self, vm: &mut R8VM, args: (x, y, z, w)) -> Result<PV> {
        featurefn!("math", {
            let e = || Err(error!(ArgTypeError,
                expect: vec![Builtin::Number,
                    Builtin::Number,
                    Builtin::Number,
                    Builtin::Number],
                got: vec![x.bt_type_of(),
                    y.bt_type_of(),
                    z.bt_type_of(),
                    w.bt_type_of()])
                .bop(Builtin::Vec4));
            let Ok(x) = x.real() else { return e() };
            let Ok(y) = y.real() else { return e() };
            let Ok(z) = z.real() else { return e() };
            let Ok(w) = w.real() else { return e() };
            Ok(vm.mem.put_pv(glam::vec4(x, y, z, w)))
        })
    }

    fn mat2_rot(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat2::from_angle(x.real()?))))
    }

    fn mat3_rot_x(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat3::from_rotation_x(x.real()?))))
    }

    fn mat3_rot_y(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat3::from_rotation_y(x.real()?))))
    }

    fn mat3_rot_z(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat3::from_rotation_z(x.real()?))))
    }

    fn mat4_rot_x(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat4::from_rotation_x(x.real()?))))
    }

    fn mat4_rot_y(&mut self, vm: &mut R8VM, args: (y)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat4::from_rotation_y(y.real()?))))
    }

    fn mat4_rot_z(&mut self, vm: &mut R8VM, args: (z)) -> Result<PV> {
        featurefn!("math", Ok(vm.mem.put_pv(glam::Mat4::from_rotation_z(z.real()?))))
    }

    fn mat(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        featurefn!("math", Ok(if args.len() == 2 {
            vm.mem.put_pv(glam::Mat2::from_cols(args[0].vec2()?, args[1].vec2()?))
        } else if args.len() == 3 {
            vm.mem.put_pv(glam::Mat3::from_cols(args[0].vec3()?, args[1].vec3()?, args[2].vec3()?))
        } else if args.len() == 4 {
            vm.mem.put_pv(glam::Mat4::from_cols(args[0].vec4()?, args[1].vec4()?, args[2].vec4()?, args[3].vec4()?))
        } else {
            return err!(ArgError, expect: ArgSpec::opt(2, 2), got_num: args.len().try_into()?)
        }))
    }

    fn translate(&mut self, vm: &mut R8VM, args: (delta)) -> Result<PV> {
        featurefn!("math", match delta {
            PV::Vec2(delta) => Ok(vm.mem.put_pv(glam::Mat3::from_translation(*delta))),
            PV::Vec3(delta) => Ok(vm.mem.put_pv(glam::Mat4::from_translation(*delta))),
            _ => err!(TypeNError,
                expect: vec![Builtin::Vec2, Builtin::Vec3],
                got: delta.bt_type_of())
        })
    }

    fn scale(&mut self, vm: &mut R8VM, args: (s)) -> Result<PV> {
        featurefn!("math", match s {
            PV::Vec2(s) => Ok(vm.mem.put_pv(glam::Mat3::from_scale(*s))),
            PV::Vec3(s) => Ok(vm.mem.put_pv(glam::Mat4::from_scale(*s))),
            _ => err!(TypeNError,
                expect: vec![Builtin::Vec2, Builtin::Vec3],
                got: s.bt_type_of())
        })
    }

    fn concat(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        join_str(args.iter().copied(), "").into_pv(&mut vm.mem)
    }

    fn error(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let argerr = |got_num| error!(ArgError,
            expect: ArgSpec::opt(1, 1),
            got_num)
        .bop(Builtin::Error);
        let mut it = args.iter().copied();
        let name_arg = it.next().ok_or_else(|| argerr(0))?;
        if let PV::Sym(name) = name_arg {
            let value = crate::nkgc::NonRef::new(it.next().unwrap_or(PV::Nil))?;
            if it.next().is_some() {
                return Err(argerr(3 + it.count() as u32))
            }
            err!(LibError, name: name.into(), value)
        } else {
            Err(error!(TypeError,
                expect: Builtin::Symbol,
                got: name_arg.bt_type_of())
                .bop(Builtin::Error)
                .argn(1))
        }
    }

    fn join(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let emap = |e: Error| e.bop(Builtin::Join).argn(1);
        let (it, sep) = match args {
            [xs, PV::Char(s)] => (xs.make_iter().map_err(emap)?,
                Cow::from(s.to_string())),
            [xs, PV::Sym(s)] => (xs.make_iter().map_err(emap)?,
                Cow::from(s.as_ref())),
            [xs, o] => (xs.make_iter().map_err(emap)?, with_ref!(*o, String(s) => {
                Ok(Cow::from(&(**s)[..]))
            }).map_err(|e| e.bop(Builtin::Join).argn(2))?),
            [xs] => (xs.make_iter()?, Cow::from("")),
            _ => return Err(error!(ArgError,
                expect: ArgSpec::opt(1, 1),
                got_num: args.len() as u32)
                .bop(Builtin::Join))
        };
        join_str(it, sep).into_pv(&mut vm.mem)
    }

    fn iter(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.make_iter().map_err(|e| e.argn(1))?.into_pv(&mut vm.mem)
    }

    fn gc(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        vm.mem.full_collection();
        Ok(PV::Nil)
    }

    fn sysrand(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        sysrand_impl().map(|r| PV::Real(r))
    }

    fn globals(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        let r = vm.globals.iter().map(|(k, _)| PV::Sym(*k)).collect::<Vec<PV>>();
        Ok(vm.mem.put_pv(r))
    }

    fn functions(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        Ok(vm.mem.put_pv(vm.get_fn_names()))
    }

    fn dump_mem(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        dbg!(&vm.mem.nuke);
        Ok(PV::Nil)
    }

    fn exit(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let status = args.first().copied()
        .unwrap_or_else(
            || PV::Sym(Builtin::KwOk.sym_id()));
        Err(Error::new(ErrorKind::Exit {
            status: status.try_into()
            .map_err(|e: Error| e.argn(1).bop(Builtin::Exit))?
        }))
    }

    fn slurp(&mut self, vm: &mut R8VM, args: (path)) -> Result<PV> {
        use std::path::PathBuf;
        let path: String = (*path).try_into()?;
        let o = std::fs::read_to_string(&path)?;
        Ok(o.into_pv(&mut vm.mem)?)
    }

    fn debug_mode(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let arg: bool = args.first()
        .cloned()
        .unwrap_or(PV::Bool(true))
        .into();
        let mut mode = VmDebugOpts::default();
        mode.show_opcodes = arg;
        mode.show_stack_on_ret = arg;
        mode.show_frames = arg;
        vm.set_debug_mode(mode);
        Ok(PV::Nil)
    }

    fn instant(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        #[cfg(not(target_arch = "wasm32"))]
        return Ok(PV::Real(vm.mem.stats().time.as_secs_f32()));
        #[cfg(target_arch = "wasm32")]
        return Ok(PV::Nil);
    }

    fn dump_macro_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        featurefn!("extra", vm.dump_macro_tbl())?;
        Ok(PV::Nil)
    }

    fn dump_sym_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        featurefn!("extra", vm.dump_symbol_tbl())?;
        Ok(PV::Nil)
    }

    fn dump_env_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        featurefn!("extra", vm.dump_env_tbl())?;
        Ok(PV::Nil)
    }

    fn dump_fn_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        featurefn!("extra", vm.dump_fn_tbl())?;
        Ok(PV::Nil)
    }

    fn disassemble(&mut self, vm: &mut R8VM, args: (func)) -> Result<PV> {
        vm.dump_fn_code((*func).try_into()?)?;
        Ok(PV::Nil)
    }

    fn dump_all_fns(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        vm.dump_all_fns()?;
        Ok(PV::Nil)
    }

    fn dump_code(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
        vm.dump_code()?;
        Ok(PV::Nil)
    }

    fn macroexpand(&mut self, vm: &mut R8VM, args: (ast)) -> Result<PV> {
        vm.macroexpand_pv(*ast, false)
    }

    fn read_compile(&mut self, vm: &mut R8VM, args: (code)) -> Result<PV> {
        with_ref_mut!(*code, String(s) => { vm.read_compile((*s).as_ref(), None) })
    }

    fn read_compile_from(&mut self, vm: &mut R8VM, args: (arg)) -> Result<PV> {
        with_ref_mut!(*arg, String(s) => {
            vm.read_compile_from(&*s)
        })
    }

    fn del(&mut self, vm: &mut R8VM, args: (tbl, key)) -> Result<PV> {
        with_ref_mut!(*tbl, Table(hm) => { Ok((*hm).remove(key)) })
        .map(|e| e.unwrap_or_default())
    }

    fn load(&mut self, vm: &mut R8VM, args: (lib)) -> Result<PV> {
        vm.load_eval((*lib).try_into()?)
    }

    fn require(&mut self, vm: &mut R8VM, args: (lib)) -> Result<PV> {
        vm.require((*lib).try_into()?)?;
        Ok(PV::Nil)
    }

    fn pow(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
        x.pow(y)
    }

    fn cos(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map(|x| PV::Real(x.cos()))
    }

    fn sin(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map(|x| PV::Real(x.sin()))
    }

    fn log10(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map(|x| PV::Real(x.log10()))
    }

    fn ln(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map(|x| PV::Real(x.ln()))
    }

    fn logn(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1))
        .and_then(|x| Ok(PV::Real(x.log(y.real().map_err(|e| e.argn(2))?))))
    }

    fn acos(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.acos()))
    }

    fn asin(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.asin()))
    }

    fn cosh(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.cosh()))
    }

    fn acosh(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.acosh()))
    }

    fn sinh(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.sinh()))
    }

    fn asinh(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.asinh()))
    }

    fn atan(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.atan()))
    }

    fn round(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.round()))
    }

    fn floor(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.floor()))
    }

    fn ceil(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.ceil()))
    }

    fn int(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.to_int().map(PV::Int)
    }

    fn atan2(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
        let x = x.real().map_err(|e| e.argn(1))?;
        let y = y.real().map_err(|e| e.argn(2))?;
        Ok(PV::Real(x.atan2(y)))
    }

    fn atanh(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.atanh()))
    }

    fn tan(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.tan()))
    }

    fn tanh(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        x.real().map_err(|e| e.argn(1)).map(|x| PV::Real(x.tanh()))
    }

    fn modulo(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
        x.modulo(y)
    }

    fn set_macro(&mut self, vm: &mut R8VM, args: (macro_name, fn_name)) -> Result<PV> {
        vm.set_macro((*macro_name).try_into()?,
            (*fn_name).try_into()?);
        Ok(PV::Nil)
    }

    fn dump_code_to(&mut self, vm: &mut R8VM, args: (to)) -> Result<PV> {
        let to = tostring(*to);
        let mut out = BufWriter::new(fs::File::create(to)?);
        vm.dump_code_to(&mut out)?;
        Ok(PV::Nil)
    }

    fn set_macro_character(&mut self, vm: &mut R8VM, args: (macro_name, fn_name)) -> Result<PV> {
        vm.set_macro_character((*macro_name).try_into()?,
            (*fn_name).try_into()?);
        Ok(PV::Nil)
    }

    fn panic(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        panic!("{}", tostring(*x))
    }

    fn is_void(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        let Ok(p) = x.ref_inner() else { return Ok(false.into()) };
        unsafe {
            if cast_mut::<Void>(p).is_some() { return Ok(true.into()) }
            let Some(obj) = cast_mut::<crate::nuke::Object>(p) else {
                return Ok(false.into())
            };
            Ok((*obj).cast::<Voided>().is_ok().into())
        }
    }

    fn is_mut_locked(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        let Ok(p) = x.ref_inner() else { return Ok(false.into()) };
        unsafe {
            let Some(obj) = cast_mut::<crate::nuke::Object>(p) else {
                return Ok(false.into())
            };
            Ok(((*obj).type_id == TypeId::of::<Locked>()).into())
        }
    }

    fn split_mut(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        let (atom, cns) = vm.mem.put(Cons { car: PV::Nil, cdr: PV::Nil });
        let pv = PV::Ref(atom);
        with_ref_mut!(*x, Cons(head) => {
            use crate::nkgc::ConsOption;
            let (a, b) = crate::r8vm::split_list(Some(head));
            unsafe {
                (*cns).car = a.as_pv();
                (*cns).cdr = b.as_pv();
            }
            Ok(pv)
        })
    }

    fn reverse_inplace(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        use crate::nkgc::ConsOption;
        if x.is_nil() {
            return Ok(*x)
        }
        with_ref_mut!(*x, Vector(xs) => {
            (*xs).reverse();
            Ok(*x)
        }, Cons(mut head) => {
            let mut xs = vec![head];
            loop {
                xs.push(head);
                if let Some(nx) = (*head).next() {
                    head = nx;
                } else {
                    break;
                }
            }
            let it = 0..xs.len();
            for (j, i) in (0..xs.len()-1).rev().zip((0..xs.len()).rev()) {
                (*xs[i]).cdr = NkAtom::make_ref(xs[j]);
            }
            (*xs[0]).cdr = PV::Nil;
            Ok(NkAtom::make_ref(xs[xs.len()-1]))
        })
    }

    fn reverse(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        use crate::nkgc::ConsOption;
        if x.is_nil() {
            return Ok(*x)
        }
        with_ref_mut!(*x, Vector(xs) => {
            let nv = (*xs).iter().copied().rev().collect::<Vec<PV>>();
            Ok(vm.mem.put_pv(nv))
        }, Cons(mut head) => {
            // Note: We _could_ avoid pushing everything, then
            // reversing, then creating the list by creating each
            // cons cell as we loop. But that gets complex with
            // the GC running underneath all this, and then
            // defending against that probably erases any
            // potential performance gain.
            let bottom = vm.mem.stack.len();
            let mut i = 1;
            vm.mem.stack.push((*head).car);
            while let Some(nx) = (*head).next() {
                vm.mem.stack.push((*nx).car);
                head = nx;
                i += 1;
            }
            vm.mem.stack[bottom..bottom+i as usize].reverse();
            vm.mem.list(i);
            Ok(vm.mem.pop().expect("expected list"))
        }, String(s) => {
            Ok(vm.mem.put_pv((*s).chars().rev().collect::<String>()))
        })
    }

    fn sort_inplace(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
        use crate::nkgc::ConsOption;
        with_ref_mut!(*x, Vector(xs) => {
            let mut res = Ok(*x);
            (*xs).sort_by(|u, v| {
                u.partial_cmp(v).unwrap_or_else(|| {
                    if res.is_ok() {
                        res = err!(IfaceNotImplemented,
                            got: vec![u.type_of().into(),
                                v.type_of().into()]).map_err(|e: Error| {
                                    e.bop(Builtin::Gte)
                                });
                    }
                    Ordering::Equal
                })
            });
            res
        }, Cons(head) => {
            merge_sort(Some(head)).map(|x| x.as_pv())
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct intern;

unsafe impl Subr for intern {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        match args {
            [s @ PV::Sym(_)] => Ok(*s),
            [r] => with_ref!(*r, String(s) => {
                if unsafe{(**s).len()} == 0 {
                    bail!(ZeroLengthSymbol);
                }
                Ok(PV::Sym(vm.mem.symdb.put_ref(&*s).id()))
            }),
            _ => Err(error!(ArgError,
                expect: ArgSpec::normal(1),
                got_num: args.len() as u32)
                .bop(Builtin::Intern))
        }
    }
    fn name(&self) -> &'static str { "intern" }
}

#[derive(Clone, Copy, Debug)]
pub struct make_table;

unsafe impl Subr for make_table {
    fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let mut hm = HMap::default();
        let mut it = args.iter();
        loop {
            let Some(k) = it.next() else { break };
            if k.is_ref() {
                return err!(KeyReference, key: k.to_string());
            }
            let Some(v) = it.next() else {
                return Err(error!(ArgError,
                    expect: ArgSpec::normal((args.len()+1) as u16),
                    got_num: args.len() as u32)
                    .bop(Builtin::MakeTable))
            };
            hm.insert(*k, *v);
        }
        Ok(vm.mem.put_pv(hm))
    }
    fn name(&self) -> &'static str { "make-table" }
}

#[derive(Clone, Copy, Debug)]
pub struct sum;

unsafe impl Subr for sum {
    fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let mut it = args.iter();
        let mut s = it.next().copied().unwrap_or(PV::Int(0));
        for i in it {
            s = s.add(i)?;
        }
        Ok(s)
    }
    fn name(&self) -> &'static str { "+" }
}

#[derive(Clone, Copy, Debug)]
pub struct sym_id;

unsafe impl Subr for sym_id {
    fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        match args {
            [PV::Sym(id)] => Ok(PV::Int(id.as_int())),
            [x] => Err(error!(TypeError,
                expect: Builtin::Symbol,
                got: x.bt_type_of(),)
                .bop(Builtin::SymID)
                .argn(1)),
            _ => ArgSpec::normal(1).check(args.len())
                                   .map_err(|e| e.bop(Builtin::SymID))
                                   .map(|_| unreachable!())
        }
    }
    fn name(&self) -> &'static str { "sym-id" }
}

#[derive(Clone, Copy, Debug)]
pub struct type_of;

unsafe impl Subr for type_of {
    fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        subr_args!((x) self _vm args { Ok(PV::Sym(x.type_of())) })
    }
    fn name(&self) -> &'static str { "type-of" }
}

#[derive(Clone, Copy, Debug)]
pub struct asum;

unsafe impl Subr for asum {
    fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        if args.len() == 1 {
            return PV::Int(0).sub(&args[0])
        }
        let mut it = args.iter();
        let mut s = it.next().ok_or(error!(ArgError,
            expect: ArgSpec::rest(1, 0),
            got_num: 0)
            .bop(Builtin::Sub))
                             .copied()?;
        for i in it {
            s = s.sub(i)?;
        }
        Ok(s)
    }
    fn name(&self) -> &'static str { "-" }
}

#[derive(Clone, Copy, Debug)]
pub struct product;

unsafe impl Subr for product {
    fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        let mut it = args.iter();
        let mut s = it.next().copied().unwrap_or(PV::Int(1));
        for i in it {
            s = s.mul(i)?;
        }
        Ok(s)
    }
    fn name(&self) -> &'static str { "*" }
}

#[derive(Clone, Copy, Debug)]
pub struct aproduct;

unsafe impl Subr for aproduct {
    fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
        if args.len() == 1 {
            return PV::Int(1).div(&args[0])
        }
        let mut it = args.iter();
        let mut s = it.next().ok_or(error!(ArgError,
            expect: ArgSpec::rest(1, 0),
            got_num: 0)
            .bop(Builtin::Div))
                             .copied()?;
        for i in it {
            s = s.div(i)?;
        }
        Ok(s)
    }
    fn name(&self) -> &'static str { "/" }
}

#[derive(Clone, Copy, Debug)]
pub struct dump_gc_stats;

unsafe impl Subr for dump_gc_stats {
    fn call(&mut self, vm: &mut R8VM, _args: &[PV]) -> Result<PV> {
        vm.println_fmt(format_args!("{:?}", vm.mem.stats()))?;
        Ok(PV::Nil)
    }
    fn name(&self) -> &'static str { "dump-gc-stats" }
}

#[derive(Clone, Copy, Debug)]
pub struct dump_stack;

unsafe impl Subr for dump_stack {
    fn call(&mut self, vm: &mut R8VM, _args: &[PV]) -> Result<PV> {
        vm.dump_stack()?;
        Ok(PV::Nil)
    }
    fn name(&self) -> &'static str { "dump-stack" }
}
