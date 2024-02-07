//! The Rodent VM

#[cfg(feature = "extra")]
use comfy_table::Table;

#[cfg(feature = "modules")]
use crate::module::{LispModule, Export, ExportKind};
use crate::{
    ast::{Excavator, Visitor, PVSrcFmt},
    chasm::{ASMOp, ChASMOpName, Lbl, ASMPV},
    builtins::Builtin,
    comp::SourceList,
    error::{Error, ErrorKind, Source, OpName, Meta, LineCol, SourceFileName, Result, SyntaxErrorKind},
    fmt::LispFmt,
    nuke::{*},
    nkgc::{Arena, Cons, SymID, PV, SPV, self, QuasiMut, Int, ConsOption, Lambda},
    string_parse::string_parse,
    subrs::{Subr, BoxSubr, FromLisp, Lispify},
    tok::Token, limits, comp::R8Compiler,
    chasm::LblMap, opt::Optomat, swym::SymRef, tokit, AsSym, IntoLisp};
use fnv::FnvHashMap;
use std::{io, fs, borrow::Cow, cmp::{self, Ordering}, collections::hash_map::Entry, convert::TryInto, fmt::{self, Debug, Display}, io::prelude::*, mem::{self, replace, take}, ptr::addr_of_mut, sync::{Mutex, atomic::AtomicU32}, path::{Path, PathBuf}, any::{TypeId, type_name}};
#[cfg(feature = "freeze")]
use serde::{Serialize, Deserialize};
use crate::stylize::Stylize;

chasm_def! {
    r8c:

    // List processing
    CNS(),
    APN(num: u32),
    LST(num: u32),
    VLT(),
    CAR(),
    CDR(),
    // SETCAR(),
    // SETCDR(),

    // Iterators
    NXT(var_idx: u16),

    // Vectors
    VEC(num: u32),
    VPUSH(),
    VPOP(),
    VGET(),
    VSET(),

    // List/vector
    LEN(),

    // Flow-control
    JMP(dip: i32),
    JV(mul: u16, max: u32),
    JT(dip: i32),
    JN(dip: i32),
    JZ(dip: i32),
    JNZ(dip: i32),
    CALL(pos: u32, nargs: u16),
    VCALL(func: u32, nargs: u16),
    APL(),
    ZCALL(nargs: u16),
    RET(),
    CCONT(dip: i32),
    UWND(),
    HCF(),

    // Stack operations
    INS(idx: u32),
    POP(num: u8),
    POPA(num_top: u16, num_pop: u16),
    SAV(num: u8),
    RST(),
    TOP(delta: u16),
    DUP(),
    // SHF(idx: u32),
    ZXP(),
    // Stack variables
    MOV(var_idx: u16),
    STR(var_idx: u16),
    // Persistent variables
    GET(env_idx: u16),
    SET(env_idx: u16),

    // Value creation
    INT(val: i32),
    FLT(val: u32),
    ARGS(nargs: u16, nopt: u16, nenv: u16, rest: u8),
    CHR(c: u32),
    CLZ(delta: i32, nenv: u16),
    ZAV(nargs: u16, nenv: u16), // Commit the closure environment
    BOOL(val: u8),
    NIL(),

    // Logic
    EQL(),
    EQP(),
    GT(),
    GTE(),
    LT(),
    LTE(),
    NOT(),

    // Math
    INC(var: u16, amount: u16),
    DEC(var: u16, amount: u16),
    ADS(dst: u16, src: u16),
    SUS(dst: u16, src: u16),
    ADD(),
    SUB(),
    DIV(),
    MUL()
}

pub type VMID = u16;
const MAX_VMS: u16 = u16::MAX;
static VM_COUNT: AtomicU32 = AtomicU32::new(0);

#[allow(unused_macros)]
macro_rules! vmprint {
    ($vm:expr, $($fmt:expr),+) => {
        $vm.print_fmt(format_args!($($fmt),+)).unwrap()
    };
}

#[allow(unused_macros)]
macro_rules! vmprintln {
    ($vm:expr, $($fmt:expr),+) => {{
        $vm.println_fmt(format_args!($($fmt),+)).unwrap();
    }};
}

#[derive(Debug, Clone)]
pub struct RuntimeError {
    pub msg: String,
    pub line: u32,
}

impl From<String> for RuntimeError {
    fn from(source: String) -> Self {
        Self { line: 0, msg: source }
    }
}

impl From<&str> for RuntimeError {
    fn from(source: &str) -> Self {
        Self { line: 0, msg: String::from(source) }
    }
}

#[cfg(feature = "extra")]
const TABLE_STYLE: &str = comfy_table::presets::UTF8_BORDERS_ONLY;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TraceFrame {
    pub src: Source,
    pub func: OpName,
    pub args: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Traceback {
    pub frames: Vec<TraceFrame>,
    pub err: Error,
}

impl RuntimeError {
    pub fn new(msg: String) -> RuntimeError {
        RuntimeError { msg, line: 0 }
    }

    pub fn err<T>(msg: String) -> std::result::Result<T, RuntimeError> {
        Err(RuntimeError::new(msg))
    }
}

fn tostring(x: PV) -> String {
    match x {
        PV::Ref(y) => match to_fissile_ref(y) {
            NkRef::String(s) => unsafe { (*s).clone() },
            _ => x.lisp_to_string(),
        },
        PV::Char(c) => format!("{c}"),
        _ => x.lisp_to_string(),
    }
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
            fn name(&self) -> &'static str { $name_s }
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

pub unsafe fn merge_sort(mut head: Option<*mut Cons>) -> Result<Option<*mut Cons>> {
    if head.is_none() || head.next().is_none() {
        return Ok(head)
    }
    let (a, b) = split_list(head);
    merge(merge_sort(a)?, merge_sort(b)?)
}

unsafe fn merge(a: Option<*mut Cons>,
                b: Option<*mut Cons>)
                -> Result<Option<*mut Cons>> {
    let Some(ap) = a else { return Ok(b) };
    let Some(bp) = b else { return Ok(a) };
    match (*ap).car.partial_cmp(&(*bp).car) {
        Some(cmp::Ordering::Greater | cmp::Ordering::Equal) => {
            (*bp).cdr = merge(a, (*bp).next())?.as_pv();
            Ok(Some(bp))
        }
        Some(cmp::Ordering::Less) => {
            (*ap).cdr = merge((*ap).next(), b)?.as_pv();
            Ok(Some(ap))
        }
        None => err!(IfaceNotImplemented,
                     got: vec![(*ap).car.type_of().into(),
                               (*bp).car.type_of().into()]).map_err(|e: Error| {
                         e.bop(Builtin::Gte)
                     })
    }
}

pub unsafe fn split_list(mut head: Option<*mut Cons>)
                         -> (Option<*mut Cons>, Option<*mut Cons>)
{
    let mut slow = head;
    let mut fast = head.next();
    while let Some(fst) = fast {
        fast = (*fst).next();
        if let Some(fst) = fast {
            slow = slow.next();
            fast = (*fst).next();
        }
    }
    let r = (head, slow.next());
    slow.map(|p| (*p).cdr = PV::Nil);
    r
}

#[allow(non_camel_case_types)]
mod sysfns {
    use std::{fmt::Write, borrow::Cow, io::BufWriter, fs, any::TypeId, hash::Hash, collections::hash_map::DefaultHasher, cmp::Ordering};

    use fnv::FnvHashMap;

    use crate::{subrs::{Subr, IntoLisp}, nkgc::{PV, Cons}, error::{Error, ErrorKind, Result}, fmt::{LispFmt, FmtWrap}, builtins::Builtin, utils::Success, nuke::{cast_mut, Void, Voided, Locked}, r8vm::merge_sort};
    use super::{R8VM, tostring, ArgSpec};

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

    std_subrs! {
        fn println(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            let s = tostring(*x);
            vm.println(&s)?;
            Ok(*x)
        }

        fn clone(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            x.deep_clone(&mut vm.mem)
        }

        fn sys_freeze(&mut self, vm: &mut R8VM, args: (_dst)) -> Result<PV> {
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

        fn string(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            x.lisp_to_string()
             .into_pv(&mut vm.mem)
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

        fn concat(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
            join_str(args.iter().copied(), "").into_pv(&mut vm.mem)
        }

        fn error(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            if let PV::Sym(name) = *x {
                err!(LibError, name: name.into())
            } else {
                Err(error!(TypeError,
                           expect: Builtin::Symbol,
                           got: x.bt_type_of())
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
                    Ok(Cow::from(&(*s)[..]))
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


        fn debug_mode(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
            let arg = args.first()
                          .cloned()
                          .unwrap_or(PV::Bool(true));
            vm.set_debug_mode(arg.into());
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
            x.real().map(|x| PV::Real(x.cos()))
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

        fn split_list(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
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
            let mut hm = FnvHashMap::default();
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
                _ => ArgSpec::normal(1).check(args.len() as u16)
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
}

pub type ArgInt = u16;

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
#[repr(C)]
pub struct ArgSpec {
    pub nargs: ArgInt,
    pub nopt: ArgInt,
    pub env: ArgInt,
    pub rest: bool,
}

impl fmt::Display for ArgSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rest {
            write!(f, "{}..", self.nargs)
        } else if self.nopt > 0 {
            write!(f, "{}..{}", self.nargs, self.nargs + self.nopt)
        } else {
            write!(f, "{}", self.nargs)
        }
    }
}

impl ArgSpec {
    pub const fn is_special(&self) -> bool {
        self.nopt > 0 || self.rest || self.env > 0
    }

    pub const fn has_opt(&self) -> bool {
        self.nopt > 0
    }

    pub const fn nopt(&self) -> usize {
        (self.nargs + self.nopt) as usize
    }

    pub const fn nargs(&self) -> usize {
        self.nargs as usize
    }

    pub const fn has_body(&self) -> bool {
        self.rest
    }

    pub const fn has_env(&self) -> bool {
        self.env > 0
    }

    pub const fn sum_nargs(&self) -> ArgInt {
        self.nargs + self.nopt + self.rest as ArgInt
    }

    pub const fn sum_stack(&self) -> ArgInt {
        self.nargs + self.nopt + self.rest as ArgInt + self.env
    }

    pub const fn is_valid_num(&self, nargs: u16) -> bool {
        (nargs == self.nargs) ||
        (self.has_body() && nargs >= self.nargs) ||
        (!self.has_body() && self.has_opt() &&
         nargs >= self.nargs && nargs <= self.nargs + self.nopt)
    }

    pub const fn normal(nargs: u16) -> ArgSpec {
        ArgSpec { nargs, nopt: 0, rest: false, env: 0 }
    }

    pub const fn opt(nargs: u16, nopt: u16) -> ArgSpec {
        ArgSpec { nargs, nopt, rest: false, env: 0 }
    }

    pub const fn rest(nargs: u16, nopt: u16) -> ArgSpec {
        ArgSpec { nargs, nopt, rest: true, env: 0 }
    }

    pub const fn any() -> ArgSpec {
        ArgSpec { nargs: 0, nopt: 0, rest: true, env: 0 }
    }

    pub const fn none() -> ArgSpec {
        ArgSpec::normal(0)
    }

    pub fn check(&self, nargs: u16) -> Result<()> {
        if self.is_valid_num(nargs) {
            Ok(())
        } else {
            Err(error!(ArgError,
                       expect: *self,
                       got_num: nargs.into()))
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Func {
    pub(crate) pos: usize,
    pub(crate) sz: usize,
    pub(crate) args: ArgSpec,
}

impl AsRef<Func> for Func {
    fn as_ref(&self) -> &Func {
        self
    }
}

#[cfg(feature = "no-threading")]
pub trait OutStream: io::Write + Debug {}
#[cfg(feature = "no-threading")]
impl<T> OutStream for T where T: io::Write + Debug {}

#[cfg(not(feature = "no-threading"))]
pub trait OutStream: io::Write + Debug + Send {}
#[cfg(not(feature = "no-threading"))]
impl<T> OutStream for T where T: io::Write + Debug + Send {}

pub trait InStream: io::Read + Debug + Send {}
impl<T> InStream for T where T: io::Read + Debug + Send {}

pub type ObjMethod = unsafe fn(*mut u8, &mut R8VM, &[PV]) -> Result<PV>;

#[derive(Debug)]
pub struct R8VM {
    /// Memory
    pub(crate) pmem: Vec<r8c::Op>,
    pub mem: Arena,
    pub(crate) globals: FnvHashMap<SymID, usize>,
    resources: FnvHashMap<TypeId, usize>,
    pub(crate) trace_counts: FnvHashMap<SymID, usize>,
    tok_tree: tokit::Fragment,
    reader_macros: FnvHashMap<String, SymID>,

    // Named locations/objects
    breaks: FnvHashMap<usize, r8c::Op>,
    macros: FnvHashMap<SymID, SymID>,
    pub(crate) funcs: FnvHashMap<SymID, Func>,
    func_labels: FnvHashMap<SymID, FnvHashMap<u32, Lbl>>,
    pub(crate) labels: LblMap,
    func_arg_syms: FnvHashMap<SymID, Vec<SymID>>,
    pub(crate) srctbl: SourceList,
    catch: Vec<usize>,
    libs: FnvHashMap<SymID, (PathBuf, fs::Metadata)>,

    obj_methods: FnvHashMap<(TypeId, SymID), ObjMethod>,

    stdout: Mutex<Box<dyn OutStream>>,

    debug_mode: bool,

    frame: usize,
}

impl Default for R8VM {
    fn default() -> Self {
        R8VM {
            pmem: Default::default(),
            resources: Default::default(),
            libs: Default::default(),
            reader_macros: Default::default(),
            tok_tree: tokit::standard_lisp_tok_tree(),
            catch: Default::default(),
            mem: Default::default(),
            globals: Default::default(),
            breaks: Default::default(),
            macros: Default::default(),
            funcs: Default::default(),
            func_labels: Default::default(),
            obj_methods: Default::default(),
            func_arg_syms: Default::default(),
            stdout: Mutex::new(Box::new(io::stdout())),
            labels: Default::default(),
            debug_mode: false,
            frame: Default::default(),
            srctbl: Default::default(),
            trace_counts: Default::default(),
        }
    }
}

struct Regs<const N: usize> {
    vals: [PV; N],
    idx: u8,
}

impl<const N: usize> Regs<N> {
    fn new() -> Regs<N> {
        Regs {
            vals: [PV::Nil; N],
            idx: 0
        }
    }

    #[inline]
    fn save(&mut self, mem: &mut Arena, num: u8) -> Result<()> {
        for i in 0..num {
            let v = mem.pop()?;
            self.vals[i as usize] = v;
            // FIXME: Regs needs to be Traceable
            assert!(!v.is_ref(), "References may not be saved.");
        }
        self.idx = num;
        Ok(())
    }

    #[inline]
    fn restore(&mut self, mem: &mut Arena) {
        for i in (0..self.idx).rev() {
            mem.push(self.vals[i as usize]);
        }
    }
}

macro_rules! call_with {
    ($vm:expr, $pos:expr, $nargs:expr, $body:block) => {{
        let frame = $vm.frame;
        $vm.frame = $vm.mem.stack.len();
        $body
        $vm.mem.push(PV::UInt(0));
        $vm.mem.push(PV::UInt(frame));
        unsafe {
            $vm.run_from_unwind($pos, frame, false)?;
        }
        let res = $vm.mem.pop().expect(
            "Function did not return a value"
        );

        res
    }};
}

// FIXME: The error handling in this macro fucks up the stack.
macro_rules! symcall_with {
    ($vm:expr, $func:expr, $nargs:expr, $body:block) => {{
        let func = $vm.funcs.get(&$func.into()).ok_or("No such function")?;
        func.args.check($nargs.try_into().unwrap()).map_err(|e| e.op($func))?;

        let frame = $vm.frame;

        $vm.frame = $vm.mem.stack.len();
        $body
        $vm.mem.push(PV::UInt(0));
        $vm.mem.push(PV::UInt(frame));
        let pos = func.pos;
        unsafe {
            $vm.run_from_unwind(pos, frame, false)?;
        }
        let res = $vm.mem.pop().expect(
            "Function did not return a value"
        );

        res
    }};
}

pub trait Args {
    fn pusharg(self, mem: &mut Arena) -> Result<()>;
    fn pusharg_ref(&self, mem: &mut Arena) -> Result<()>;
    fn nargs(&self) -> usize;
}

pub trait AsArgs {
    fn inner_pusharg(self, mem: &mut Arena) -> Result<()>;
    fn inner_nargs(&self) -> usize;
}

impl<T> AsArgs for T where T: Args {
    #[inline(always)]
    fn inner_pusharg(self, mem: &mut Arena) -> Result<()> {
        self.pusharg(mem)
    }

    #[inline(always)]
    fn inner_nargs(&self) -> usize {
        self.nargs()
    }
}

impl AsArgs for Box<dyn Args + Send> {
    fn inner_pusharg(self, mem: &mut Arena) -> Result<()> {
        self.pusharg_ref(mem)
    }

    fn inner_nargs(&self) -> usize {
        self.nargs()
    }
}

impl Args for &[PV] {
    fn pusharg(self, mem: &mut Arena) -> Result<()> {
        for arg in self.iter().copied() {
            mem.push(arg);
        }
        Ok(())
    }

    fn pusharg_ref(&self, mem: &mut Arena) -> Result<()> {
        for arg in self.iter() {
            mem.push(*arg);
        }
        Ok(())
    }

    fn nargs(&self) -> usize {
        self.len()
    }
}

impl<const N: usize> Args for &[PV; N] {
    fn pusharg(self, mem: &mut Arena) -> Result<()> {
        for arg in self.iter().copied() {
            mem.push(arg);
        }
        Ok(())
    }

    fn pusharg_ref(&self, mem: &mut Arena) -> Result<()> {
        for arg in self.iter() {
            mem.push(*arg);
        }
        Ok(())
    }

    fn nargs(&self) -> usize {
        self.len()
    }
}

macro_rules! impl_args_tuple {
    ($($arg:ident),*) => {
        #[allow(non_snake_case)]
        impl<$($arg),*> Args for ($($arg),*,)
            where $($arg: crate::subrs::IntoLisp + crate::subrs::RefIntoLisp ),*
        {
            fn pusharg(self, mem: &mut Arena) -> Result<()> {
                let ($($arg),*,) = self;
                $(let $arg = $arg.into_pv(mem)?;
                  mem.push($arg);)*
                Ok(())
            }

            fn pusharg_ref(&self, mem: &mut Arena) -> Result<()> {
                let ($($arg),*,) = self;
                $(let $arg = $arg.ref_into_pv(mem)?;
                  mem.push($arg);)*
                Ok(())
            }

            fn nargs(&self) -> usize {
                count_args!($($arg),*)
            }
        }
    };
}

impl Args for () {
    fn pusharg(self, _mem: &mut Arena) -> Result<()> { Ok(()) }
    fn pusharg_ref(&self, _mem: &mut Arena) -> Result<()> { Ok(()) }
    fn nargs(&self) -> usize { 0 }
}

impl_args_tuple!(X);
impl_args_tuple!(X, Y);
impl_args_tuple!(X, Y, Z);
impl_args_tuple!(X, Y, Z, W);
impl_args_tuple!(X, Y, Z, W, A);
impl_args_tuple!(X, Y, Z, W, A, B);
impl_args_tuple!(X, Y, Z, W, A, B, C);
impl_args_tuple!(X, Y, Z, W, A, B, C, D);
impl_args_tuple!(X, Y, Z, W, A, B, C, D, E);
impl_args_tuple!(X, Y, Z, W, A, B, C, D, E, F);
impl_args_tuple!(X, Y, Z, W, A, B, C, D, E, F, G);
impl_args_tuple!(X, Y, Z, W, A, B, C, D, E, F, G, H);

pub trait NArgs<A> {
    fn pusharg(self, mem: &mut Arena) -> Result<()>;
    fn nargs(&self) -> usize;
}

macro_rules! impl_nargs {
    ($nargs:literal, $($t:tt($($ts:tt),+)),+) => {
        #[allow(non_snake_case)]
        impl<$($t, $($ts),+),+> NArgs<($($($ts),+),*)> for ($($t,)*)
            where $($t: Lispify<$($ts),*>),+
        {
            #[inline]
            fn pusharg(self, mem: &mut Arena) -> Result<()> {
                let ($($t,)*) = self;
                $(let $t = $t.lispify(mem)?; mem.push($t);)*
                Ok(())
            }

            #[inline]
            fn nargs(&self) -> usize {
                $nargs
            }
        }
    };
}

impl NArgs<()> for () {
    fn pusharg(self, _mem: &mut Arena) -> Result<()> { Ok(()) }
    fn nargs(&self) -> usize { 0 }
}

impl_nargs!(1,A(A0,A1,A2));
impl_nargs!(2,A(A0,A1,A2),B(B0,B1,B2));
impl_nargs!(3,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2));
impl_nargs!(4,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2));
impl_nargs!(5,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2));
impl_nargs!(6,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2));
impl_nargs!(7,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2),G(G0,G1,G2));
impl_nargs!(8,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2),G(G0,G1,G2),H(H0,H1,H2));
impl_nargs!(9,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2),G(G0,G1,G2),H(H0,H1,H2),I(I0,I1,I2));
impl_nargs!(10,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2),G(G0,G1,G2),H(H0,H1,H2),I(I0,I1,I2),J(J0,J1,J2));
impl_nargs!(11,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2),G(G0,G1,G2),H(H0,H1,H2),I(I0,I1,I2),J(J0,J1,J2),K(K0,K1,K2));
impl_nargs!(12,A(A0,A1,A2),B(B0,B1,B2),C(C0,C1,C2),D(D0,D1,D2),E(E0,E1,E2),F(F0,F1,F2),G(G0,G1,G2),H(H0,H1,H2),I(I0,I1,I2),J(J0,J1,J2),K(K0,K1,K2),L(L0,L1,L2));

#[cfg(not(feature = "no-threading"))]
unsafe impl Send for R8VM {}

// NOTE: This only applies to calls made with apply_spv, calls internally in the
// VM bytecode are unbounded.
const MAX_CLZCALL_ARGS: u16 = 32;

fn sexpr_modifier_bt(tok: &str) -> Option<Builtin> {
    Some(match tok {
        "'" => Builtin::Quote,
        "`" => Builtin::Quasi,
        "," => Builtin::Unquote,
        ",@" => Builtin::USplice,
        _ => return None,
    })
}

#[inline]
const fn clzcall_pad_dip(nargs: u16) -> usize {
    debug_assert!(nargs <= MAX_CLZCALL_ARGS);
    // NOTE: See R8VM::new, it creates a MAX_CLZCALL_ARGS number of
    // CLZCALL(n)/RET bytecodes after the first HCF bytecode.
    1 | (nargs as usize) << 1
}

#[derive(Debug, Clone, Copy)]
pub enum LibrarySrc<'a> {
    New(&'a Path),
    Exists(&'a Path),
}

impl<'a> AsRef<Path> for LibrarySrc<'a> {
    fn as_ref(&self) -> &'a Path {
        match self {
            LibrarySrc::New(p) => p,
            LibrarySrc::Exists(p) => p,
        }
    }
}

impl<'a> TryInto<SourceFileName> for LibrarySrc<'a> {
    type Error = Error;

    fn try_into(self) -> std::result::Result<SourceFileName, Self::Error> {
        let Ok(s) = self.as_ref().to_owned().into_os_string().into_string() else {
            bail!(Utf8DecodingError)
        };
        Ok(Some(Cow::from(s)))
    }
}

impl R8VM {
    pub fn no_std() -> R8VM {
        let mut vm = R8VM {
            pmem: vec![r8c::Op::HCF()],
            ..Default::default()
        };

        for i in 0..=MAX_CLZCALL_ARGS {
            let pos = vm.pmem.len();
            vm.pmem.push(r8c::Op::ZCALL(i));
            vm.pmem.push(r8c::Op::RET());
            let sym = vm.mem.symdb.put(format!("<ζ>-λ/{i}")).id();
            vm.funcs.insert(sym, Func {
                pos,
                sz: 2,
                args: ArgSpec::normal(0)
            });
        }

        vm.funcs.insert(Builtin::HaltFunc.sym_id(), Func {
            pos: 0,
            sz: 1,
            args: ArgSpec::none()
        });

        macro_rules! addfn {
            ($name:ident) => {
                addfn!(stringify!($name), $name);
            };

            ($name:expr, $fn:ident) => {
                let sym = vm.mem.symdb.put_ref($name).id();
                vm.set(sym, (sysfns::$fn).into_subr()).unwrap();
            };
        }

        // IO
        addfn!(println);
        addfn!(print);

        // Modules
        #[cfg(any(not(target_arch = "wasm32"), target_os = "wasi"))] {
            addfn!(load);
            addfn!(require);
            addfn!(instant);
            addfn!("read-from", read_from);
            addfn!("read-compile-from", read_compile_from);
        }

        // Meta
        addfn!(eval);
        addfn!(read);
        addfn!(macroexpand);
        addfn!(clone);
        addfn!(intern);
        addfn!(gc);
        addfn!("sys/freeze", sys_freeze);
        addfn!("read-compile", read_compile);
        addfn!("type-of", type_of);
        addfn!("sym-id", sym_id);
        addfn!("sys/set-macro", set_macro);
        addfn!("sys/set-macro-character", set_macro_character);
        addfn!("void?", is_void);
        addfn!("mut-locked?", is_mut_locked);

        // Debug
        #[cfg(feature = "extra")] {
            addfn!("dump-fns", dump_all_fns);
            addfn!("dump-code-to", dump_code_to);
            addfn!("dump-code", dump_code);
            addfn!("dump-macro-tbl", dump_macro_tbl);
            addfn!("dump-sym-tbl", dump_sym_tbl);
            addfn!("dump-env-tbl", dump_env_tbl);
            addfn!("dump-fn-tbl", dump_fn_tbl);
            addfn!("dump-gc-stats", dump_gc_stats);
            addfn!("dump-stack", dump_stack);
            #[cfg(debug_assertions)]
            addfn!("debug-mode", debug_mode);
            addfn!(disassemble);
            addfn!("dump-mem", dump_mem);
        }

        // Tables
        addfn!("make-table", make_table);
        addfn!(del);

        // Control-Flow
        addfn!(panic);
        addfn!(error);
        addfn!(exit);

        // Arithmetic
        addfn!("%", modulo);
        addfn!("+", sum);
        addfn!("-", asum);
        addfn!("*", product);
        addfn!("/", aproduct);
        addfn!(pow);
        addfn!(vec2);
        addfn!(vec3);
        addfn!(vec4);
        addfn!(cos);
        addfn!(sin);
        addfn!(log10);
        addfn!(logn);
        addfn!(acos);
        addfn!(asin);
        addfn!(cosh);
        addfn!(acosh);
        addfn!(sinh);
        addfn!(asinh);
        addfn!(atan);
        addfn!(atanh);
        addfn!(ln);
        addfn!(tan);
        addfn!(tanh);

        // Strings
        addfn!(string);
        addfn!(concat);
        addfn!(join);

        // Iter
        addfn!(iter);

        // Utils
        addfn!("sort!", sort_inplace);
        addfn!("split!", split_list);

        let src = Some(Cow::Borrowed("<ζ>::boot-stage0"));
        vm.read_compile(include_str!("../lisp/boot-stage0.lisp"),
                        src.clone()).unwrap();

        vm
    }

    fn resource_idx<T: Userdata>(&mut self) -> u32 {
        match self.resources.entry(TypeId::of::<T>()) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                log::trace!("new resource {}", type_name::<T>());
                let idx = self.mem.push_env(PV::Nil);
                *e.insert(idx)
            },
        }.try_into().unwrap()
    }

    #[cfg(feature = "derive")]
    pub fn bind_resource_fns<T, K>(&mut self, override_prefix: Option<&'static str>)
        where T: Userdata + crate::records::MethodSet<K> + crate::records::KebabTypeName
    {
        let obj_idx = self.resource_idx::<T>();
        let sep = if override_prefix.is_some() { "" } else { "/" };
        let prefix = override_prefix.unwrap_or(T::kebab_type_name());
        log::trace!("bind resource functions {} at {}", type_name::<T>(), obj_idx);
        for (name, spec, _fn) in T::methods() {
            assert!(name.len() > 1, "Empty method name");
            let name_no_kw = &name[1..];
            let fn_name = self.sym_id(&format!("{prefix}{sep}{name_no_kw}"));
            let kwname = self.sym_id(name);
            let name_idx = self.mem.push_env(PV::Sym(kwname));
            let fn_pos = self.pmem.len();
            self.pmem.push(r8c::Op::GET(obj_idx as u16));
            self.pmem.push(r8c::Op::INS(name_idx as u32));
            assert!(!spec.is_special(), "No special function signatures allowed for methods");
            for i in 0..spec.nargs {
                self.pmem.push(r8c::Op::MOV(i));
            }
            self.pmem.push(r8c::Op::ZCALL(spec.nargs + 1));
            self.pmem.push(r8c::Op::RET());
            let sz = self.pmem.len() - fn_pos;
            // TODO: Add arg names, they have to be generated in the methods proc-macro
            self.defun(fn_name, *spec, vec![], fn_pos, sz);
        }
    }

    pub unsafe fn set_resource<T: Userdata>(&mut self, rf: &mut T) {
        let obj = rf.into_pv(&mut self.mem).unwrap();
        let idx = self.resource_idx::<T>();
        self.mem.set_env(idx as usize, obj);
    }

    pub unsafe fn call_method_w_keys(&mut self, key: (TypeId, SymID), mem: *mut u8, args: &[PV]) -> Result<PV> {
        match self.obj_methods.get(&key) {
            Some(f) => (f)(mem, self, args),
            None => err!(NoSuchMethod,
                         strucc: "unknown", // FIXME
                         method: key.1.into()),
        }
    }

    pub unsafe fn call_method(&mut self, ip: *mut r8c::Op, obj: *mut Object, args: &[PV]) -> Result<PV> {
        let kw = args.first()
                     .ok_or_else(|| error!(NoMethodGiven, vt: (*obj).vt))
                     .and_then(|f| f.sym())?;
        let key = ((*obj).type_id , kw);
        match self.obj_methods.get(&key) {
            Some(f) => (f)((*obj).mem, self, &args[1..]).map_err(|e| {
                let ipd = self.ip_delta(ip) - 1;
                e.insert_traceframe(self.get_source(ipd),
                                    OpName::OpStr((*obj).vt.type_name),
                                    &args[..])
            }),
            // FIXME: Check if object is locked here, and give a different error
            None => if (*obj).type_id == TypeId::of::<Locked>() {
                err!(MutLocked, vt: (*obj).vt)
            } else {
                err!(NoSuchMethod,
                     strucc: (*obj).vt.type_name,
                     method: key.1.into())
            }
        }
    }

    pub fn register_method<T: 'static>(&mut self, name: impl AsSym, m: ObjMethod) {
        let sym = name.as_sym(self);
        self.obj_methods.insert((TypeId::of::<T>(), sym), m);
    }

    pub fn dump_code_to(&self, out: &mut dyn Write) -> Result<()> {
        for op in self.pmem.iter() {
            op.write(out)?;
        }
        Ok(())
    }

    pub fn new() -> R8VM {
        let mut vm = R8VM::no_std();

        let src = Some(Cow::Borrowed("<ζ>-core"));
        let core = include_str!("../lisp/core.lisp");
        vm.read_compile(core, src).unwrap();

        vm
    }

    pub fn has_mut_extrefs(&self) -> bool {
        self.mem.has_mut_extrefs()
    }

    pub fn minimize(&mut self) {
        self.mem.minimize();
        self.pmem.shrink_to_fit();
        self.globals.shrink_to_fit();
        self.breaks.shrink_to_fit();
        self.funcs.shrink_to_fit();
        self.func_labels.shrink_to_fit();
    }

    pub fn set<A, R, N>(&mut self, var: SymID, obj: impl Lispify<A, R, N>) -> Result<()> {
        let pv = obj.lispify(&mut self.mem)?;
        let idx = self.mem.push_env(pv);
        self.globals.insert(var, idx);
        Ok(())
    }

    pub fn add_subr(&mut self, subr: impl Subr) {
        let name = self.mem.symdb.put_ref(subr.name()).id();
        self.set(name, subr.into_subr())
            .expect("Can't allocate Subr");
    }

    pub fn set_debug_mode(&mut self, debug_mode: bool) {
        self.debug_mode = debug_mode;
    }

    pub fn get_debug_mode(&self) -> bool {
        self.debug_mode
    }

    pub fn catch(&mut self) {
        let top = self.mem.stack.len();
        self.catch.push(top)
    }

    pub fn catch_pop(&mut self) {
        self.catch.pop();
    }

    pub fn unwind(&mut self) {
        let top_v = self.mem.stack.last().copied();
        let catchp = self.catch.pop().unwrap_or(0);
        unsafe {
            self.mem.stack.set_len(catchp);
        }
        if let Some(pv) = top_v {
            self.mem.stack.push(pv);
        }
    }

    pub fn get_func(&self, name: SymID) -> Option<&Func> {
        self.funcs.get(&name)
    }

    /// Find a library by name, returns the path to the library as a LibrarySrc,
    /// which will be New(path) if the file is modified or has not been loaded,
    /// or Exists(path) if the file is already loaded and has not been modified.
    pub fn find_lib_src(&mut self, lib: SymID) -> Result<LibrarySrc> {
        let it = self.var(Builtin::SysLoadPath.sym_id())?
                     .make_iter()
                     .map_err(|e| e.bop(Builtin::SysLoad))?;
        for (i, p) in it.enumerate() {
            let mut path = PathBuf::from(with_ref!(p, String(s) => {Ok(&(*s)[..])})
                                         .map_err(|e| e.argn(i as u32)
                                                  .bop(Builtin::SysLoadPath))?);
            for ext in &["sp", "lisp"] {
                path.push(format!("{}.{ext}", lib.as_ref()));
                if let Ok(meta) = fs::metadata(&path) {
                    if meta.is_file() {
                        match self.libs.entry(lib) {
                            Entry::Occupied(mut e) => {
                                if e.get().1.modified()? == meta.modified()? {
                                    return Ok(LibrarySrc::Exists(self.libs[&lib].0.as_ref()));
                                }
                                e.insert((path, meta));
                            },
                            Entry::Vacant(e) => {
                                e.insert((path, meta));
                            },
                        }
                        return Ok(LibrarySrc::New(self.libs[&lib].0.as_ref()));
                    }
                }
                path.pop();
            }
        }
        err!(ModuleNotFound, lib: lib.into())
    }

    pub fn require(&mut self, lib: SymID) -> Result<()> {
        let LibrarySrc::New(path) = self.find_lib_src(lib).map(|x| x.clone())? else {
            return Ok(())
        };
        let src = fs::read_to_string(path)?;
        let Ok(s) = path.to_owned().into_os_string().into_string() else {
            bail!(Utf8DecodingError)
        };
        // let src_name = path.try_into()?;
        self.read_compile(&src, Some(Cow::from(s)))?;
        Ok(())
    }

    pub fn load_eval(&mut self, lib: SymID) -> Result<PV> {
        let path = self.find_lib_src(lib)?;
        let src = fs::read_to_string(path)?;
        let src_name = path.try_into()?;
        self.read_compile(&src, src_name)
    }

    pub fn var(&self, sym: SymID) -> Result<PV> {
        let idx = self.get_env_global(sym)
                      .ok_or(error!(UndefinedVariable, var: sym.into()))?;
        Ok(self.mem.get_env(idx))
    }

    pub fn get_env_global(&self, name: SymID) -> Option<usize> {
        self.globals.get(&name).copied()
    }

    /// Reads LISP code into an AST.
    pub fn read(&mut self, sexpr: &str) -> Result<PV> {
        unimplemented!();
        // self.read_compile(&format!("'({sexpr})"), None)
    }

    /// Reads LISP code into an AST from file.
    pub fn read_from(&mut self, path: impl AsRef<Path>) -> Result<PV> {
        unimplemented!();
        // let sexpr = fs::read_to_string(path.as_ref())?;
        // let name = path.as_ref().file_stem().map(|p| {
        //     p.to_string_lossy().into_owned()
        // }).map(Cow::from);
        // self.read_compile(&format!("'({sexpr})"), name)
    }

    pub fn read_compile_from(&mut self, path: impl AsRef<Path>) -> Result<PV> {
        let sexpr = fs::read_to_string(path.as_ref())?;
        let name = path.as_ref().file_stem().map(|p| {
            p.to_string_lossy().into_owned()
        }).map(Cow::from);
        self.read_compile(&sexpr, name)
    }

    pub fn read_compile(&mut self, sexpr: &str, file: SourceFileName) -> Result<PV> {
        let tok_tree = self.tok_tree.clone();
        let mut tokit = tokit::Toker::new(sexpr, &tok_tree);
        let mut mods: Vec<SymID> = vec![];
        let mut close = vec![];
        let mut pmods = vec![];
        let mut dots = vec![];
        let mut dot = None;
        let mut num: u32 = 0;
        let mut srcs = vec![];
        let mut src_idxs = vec![0];
        let mut cc = R8Compiler::new(self);
        macro_rules! wrap {
            ($push:expr) => {{
                $push;
                while let Some(op) = mods.pop() {
                    let p = self.mem.pop().expect("No expr to wrap");
                    match Builtin::from_sym(op) {
                        Some(op @ (Builtin::Unquote | Builtin::USplice)) => {
                            let intr = Intr { op, arg: p };
                            self.mem.push_new(intr);
                        }
                        _ => {
                            self.mem.push(PV::Sym(op));
                            self.mem.push(p);
                            self.mem.list(2);
                        }
                    }
                }
            }};
        }
        macro_rules! assert_no_trailing {
            ($($meta:expr),*) => {
                if !mods.is_empty() {
                    let mods = mods.into_iter()
                                   .map(|s| s.to_string())
                                   .collect::<Vec<_>>()
                                   .join("");
                    return Err(error!(TrailingModifiers, mods)$(.amend($meta))*);
                }
            };
        }
        let mut modfn_pos = 0;
        while let Some(tok) = tokit.next() {
            let Token { line, col, text } = tok;
            srcs.push(LineCol { line, col });
            match text {
                "(" => {
                    src_idxs.push(srcs.len());
                    pmods.push(take(&mut mods));
                    close.push(num + 1);
                    dots.push(dot);
                    dot = None;
                    num = 0;
                }
                ")" if close.is_empty() => bail!(TrailingDelimiter { close: ")" }),
                "." if close.is_empty() => bail!(OutsideContext {
                    ctx: Builtin::List,
                    op: Builtin::ConsDot
                }),
                "." if dot.is_some() => bail!(SyntaxError(SyntaxErrorKind::DotAfterDot)),
                "." => {
                    if tokit.peek().map(|t| t.text == ")").unwrap_or_default() {
                        bail!(SyntaxError(SyntaxErrorKind::DotAtEndOfList))
                    }

                    if !mods.is_empty() {
                        bail!(SyntaxError(SyntaxErrorKind::ModifierBeforeDot))
                    }

                    dot = Some(num)
                },
                ")" => {
                    if let Some(dot_at) = dot {
                        if dot_at != num-1 {
                            bail!(SyntaxError(SyntaxErrorKind::MoreThanOneElemAfterDot))
                        }
                    }
                    assert_no_trailing!(Meta::Source(LineCol { line, col }));
                    let src_idx = src_idxs.pop().unwrap();
                    let fst_src = srcs[src_idx].into_source(file.clone());
                    let cur_srcs = srcs.drain(src_idx..)
                                       .map(|lc| lc.into_source(file.clone()));
                    mods = pmods.pop().expect("Unable to wrap expr");
                    if num > 0 && close.len() == 1 {
                        let v = if mods.is_empty() {
                            let idx = self.mem.stack.len() - num as usize;
                            let stack = take(&mut self.mem.stack);
                            for (pv, src) in stack[idx..].iter().zip(cur_srcs) {
                                pv.tag(&mut self.mem, src);
                            }
                            let _ = replace(&mut self.mem.stack, stack);
                            self.expand_from_stack(num, dot.is_some())?
                        } else {
                            wrap!(self.mem.list_dot_srcs(num, cur_srcs, dot.is_some()));
                            let pv = self.mem.pop().unwrap();
                            self.macroexpand_pv(pv, false)?
                        };
                        // dbg!(PVSrcFmt { v, mem: &self.mem }.lisp_to_string());
                        // ^ macroexpand can eval/defun, so update offsets
                        cc.set_offsets(self);

                        // FIXME: This is SLOW and has to be REMOVED removed
                        cc.update_globals(self);

                        let excv = Excavator::new(&self.mem);
                        let mut ast = excv.to_ast(v, fst_src)?;
                        //dbg!(&ast);
                        self.mem.clear_tags();
                        let mut opto = Optomat::new();
                        opto.visit(&mut ast)?;
                        if tokit.peek().is_some() {
                            cc.compile_top(ast)?;
                        } else {
                            modfn_pos = cc.compile_top_tail(ast)?;
                        }
                        cc.take(self)?;
                    } else {
                        wrap!(self.mem.list_dot_srcs(num, cur_srcs, dot.is_some()));
                    }

                    dot = dots.pop().unwrap();
                    num = close.pop()
                               .ok_or_else(
                                   || error!(TrailingDelimiter, close: ")")
                                       .amend(Meta::Source(LineCol { line, col })))?;
                }
                _ => {
                    let sexpr_mod = sexpr_modifier_bt(text)
                        .map(|b| b.sym_id())
                        .or_else(|| {
                            self.reader_macros.get(text).copied()
                        });
                    let pv = if let Some(m) = sexpr_mod {
                        mods.push(m);
                        continue;
                    } else if let Ok(int) = text.parse() {
                        PV::Int(int)
                    } else if let Ok(num) = text.parse() {
                        PV::Real(num)
                    } else if let Some(strg) = tok.inner_str() {
                        self.mem.put_pv(string_parse(&strg)?)
                    } else if text == "true" {
                        PV::Bool(true)
                    } else if text == "false" {
                        PV::Bool(false)
                    } else if text == "nil" {
                        PV::Nil
                    } else {
                        PV::Sym(self.mem.symdb.put_ref(text).id())
                    };

                    if !close.is_empty() {
                        wrap!(self.mem.push(pv));
                    } else if tokit.peek().is_none() {
                        wrap!(self.mem.push(pv));
                        let pv = self.mem.pop().unwrap();
                        let excv = Excavator::new(&self.mem);
                        let src = LineCol { line, col }.into_source(file.clone());
                        let ast = excv.to_ast(pv, src)?;
                        modfn_pos = cc.compile_top_tail(ast)?;
                        cc.take(self)?;
                    } else {
                        continue;
                    }

                    num += 1;
                }
            }
        }
        tokit.check_error().map_err(|e| if let Some(file) = file {
            e.amend(Meta::SourceFile(file))
        } else { e })?;
        if !close.is_empty() {
            bail!(UnclosedDelimiter { open: "(" })
        }
        assert_no_trailing!();
        if modfn_pos != 0 {
            Ok(call_with!(self, modfn_pos, 0, {}))
        } else {
            Ok(PV::Nil)
        }
    }

    fn expand_from_stack(&mut self, n: u32, dot: bool) -> Result<PV> {
        let op = self.mem.from_top(n as usize);
        let v = if let Some(m) = op.sym().ok().and_then(|op| self.macros.get(&op)).copied() {
            if dot {
                return Err(error!(UnexpectedDottedList,).bop(Builtin::Apply))
            }
            let func = self.funcs.get(&m).ok_or("No such function")?;
            let chk = func.args.check((n - 1) as u16).map_err(|e| e.op(m));
            if let Err(e) = chk {
                self.mem.popn(n as usize);
                return Err(e);
            }
            let frame = self.frame;
            self.frame = self.mem.stack.len() - (n as usize) + 1;
            self.mem.push(PV::UInt(0));
            self.mem.push(PV::UInt(frame));
            let pos = func.pos;
            unsafe { self.run_from_unwind(pos, frame, true)?; }
            let res = self.mem.pop().expect("Function did not return a value");
            self.mem.pop().expect("op name missing from stack");
            res
        } else {
            let top = self.mem.stack.len();
            for i in top - (n as usize) .. top {
                let v = self.mem.stack[i];
                match self.macroexpand_pv(v, false) {
                    Ok(nv) => self.mem.stack[i] = nv,
                    Err(e) => {
                        self.mem.popn(n as usize);
                        return Err(e)
                    }
                }
            }
            self.mem.list_dot(n, dot); // FIXME: Source info???
            self.mem.pop().unwrap()
        };
        self.macroexpand_pv(v, false)
    }

    fn varor<T>(&mut self, name: SymID, or_default: T) -> Result<T>
        where PV: FromLisp<T>
    {
        if let Ok(var) = self.var(name) {
            var.from_lisp(&mut self.mem)
               .map_err(|e| e.amend(Meta::VarName(OpName::OpSym(name.into()))))
        } else {
            Ok(or_default)
        }
    }

    fn macroexpand_pv(&mut self, mut v: PV, quasi: bool) -> Result<PV> {
        // This function is tricky, any time macroexpand_pv is executed
        // recursively, or when run_from_unwind is executed, all local variables
        // of type PV may have their pointers become invalidated. Any time you
        // call this function recursively or otherwise execute code, you must
        // first back up any PV values on the SPAIK stack with
        // `self.mem.stack.push(v)` and then recover them by popping from the
        // stack. Doing otherwise is UB.

        let ind_lim = self.varor(Builtin::LimitsMacroexpandRecursion.sym_id(),
                                 limits::MACROEXPAND_RECURSION)?;

        if quasi {
            if let Some(QuasiMut::Unquote(s) | QuasiMut::USplice(s)) = v.quasi_mut() {
                self.mem.stack.push(v);
                let nv = unsafe { self.macroexpand_pv(*s, false)? };
                invalid!(v, s); // macroexpand_pv
                let mut v = self.mem.stack.pop().unwrap();
                v.intr_set_inner(nv);
                return Ok(v)
            }
        } else {
            let mut inds = 0;
            let src = self.mem.get_pv_tag(v).cloned();
            // Keep expanding until the result can no longer be macro-expanded
            while let Some(m) = v.op().and_then(|op| self.macros.get(&op)).copied() {
                // `op` is the macro name, and `m` is the underlying function
                // for the macro (it may be undefined,) find the function
                let func = self.funcs.get(&m).ok_or("No such function")?;
                let mut nargs = 0;

                // Back up previous call-frame and set new one for macro
                let frame = self.frame;
                self.frame = self.mem.stack.len();

                // Push arguments to macro function
                for arg in v.args() {
                    self.mem.push(arg);
                    nargs += 1;
                }

                // Check for correct number of arguments
                if let Err(e) = func.args.check(nargs).map_err(|e| e.op(m)) {
                    // Pop arguments off stack again in case of error, and
                    // restore call-frame
                    self.mem.popn(nargs as usize);
                    self.frame = frame;
                    return Err(e);
                }

                // Push previous call-frame and run macro
                self.mem.push(PV::UInt(0));
                self.mem.push(PV::UInt(frame));
                unsafe { self.run_from_unwind(func.pos, frame, true)?; }

                // Set new expand-candidate to the result of the macro
                invalid!(v); // run_from_unwind
                v = self.mem.pop().expect("Function did not return a value");
                if let Some(ref src) = src {
                    self.mem.tag_pv(v, src.clone());
                }

                // This may loop infinitely if a macro expands to itself, so
                // check if we're at macro recursion limit
                inds += 1;
                if inds > ind_lim {
                    return err!(MacroexpandRecursionLimit, lim: ind_lim);
                }
            }
        }

        let bop = v.bt_op();
        if bop == Some(Builtin::Quote) {
            // Quoted list, no expansion
            Ok(v)
        } else if bop == Some(Builtin::Quasi) {
            // Quasi-quoted list, expand (cdr v)
            self.mem.stack.push(v);
            let ni = self.macroexpand_pv(v.inner()?, true)?;
            invalid!(v); // macroexpand_pv
            v = self.mem.stack.pop().unwrap();
            v.set_inner(ni)?;
            Ok(v)
        } else if v.is_atom() {
            // Atomic, e.g number or symbol, no expansion
            Ok(v)
        } else {
            // Expand each element of the list
            self.mem.push(v);
            // Is this the final element of a dotted list e.g we are at 3 in (1 2 . 3)
            let mut dot = false;
            // Index in list
            let mut idx = 0;
            loop {
                let PV::Ref(p) = v else { unreachable!("{v:?}") };
                let Cons { car, cdr } = unsafe { *fastcast(p) };
                let r = if dot {cdr} else {car};
                let ncar = match (bop, idx) {
                    // We ignore (lambda <args> ...) and (define <var> ...)
                    (Some(Builtin::Lambda), 1) |
                    (Some(Builtin::Define), 1) => Ok(r),
                    // Expand element
                    _ => {
                        self.mem.push(v);
                        let ncar = self.macroexpand_pv(r, quasi);
                        v = self.mem.pop().unwrap();
                        ncar
                    }
                };
                invalid!(car, cdr, r); // ^ macroexpand_pv
                let ncar = match ncar {
                    Ok(x) => x,
                    Err(e) => {
                        self.mem.pop().unwrap();
                        return Err(e)
                    }
                };
                let PV::Ref(p) = v else { unreachable!() };
                let cns = unsafe { fastcast_mut::<Cons>(p) };
                unsafe {
                    // Replace car with expanded code, unless we are at the end
                    // of a dotted list, then we replace cdr
                    if dot {
                        (*cns).cdr = ncar;
                    } else {
                        (*cns).car = ncar;
                    }

                    idx += 1;
                    v = match (*cns).cdr.bt_type_of() {
                        Builtin::Nil => break,
                        Builtin::Cons => (*cns).cdr,
                        // No cons, but we are at end of dotted list, so we're done
                        _ if dot => break,
                        // No cons, it is a dotted list
                        _ => { dot = true; v }
                    }
                }
            }
            self.mem.pop()
        }
    }

    fn get_source(&self, idx: usize) -> Source {
        let src_idx = match self.srctbl.binary_search_by(|(u, _)| u.cmp(&idx)) {
            Ok(i) => i,
            Err(i) => (i as isize - 1).max(0) as usize
        };
        self.srctbl[src_idx].1.clone()
    }

    pub fn eval(&mut self, expr: &str) -> Result<PV> {
        self.read_compile(expr, None)
    }

    pub fn set_macro(&mut self, macro_sym: SymID, fn_sym: SymID) {
        self.macros.insert(macro_sym, fn_sym);
    }

    pub fn set_macro_character(&mut self, macro_sym: SymID, fn_sym: SymID) {
        let s = macro_sym.to_string();
        self.tok_tree.insert(&s);
        self.reader_macros.insert(s, fn_sym);
    }

    pub fn defvar(&mut self, name: SymID, idx: usize, pos: usize) -> Result<()> {
        let res = call_with!(self, pos, 0, {});
        self.mem.set_env(idx, res);
        self.globals.insert(name, idx);
        Ok(())
    }

    pub fn defun(&mut self,
                 name: SymID,
                 args: ArgSpec,
                 arg_names: Vec<SymID>,
                 pos: usize,
                 sz: usize)
    {
        match self.funcs.entry(name) {
            Entry::Occupied(mut e) => {
                let ppos = e.get().pos as u32;
                use r8c::Op::*;
                for op in self.pmem.iter_mut() {
                    *op = match *op {
                        CALL(p, nargs) if p == ppos => CALL(pos as u32, nargs),
                        op => op,
                    }
                }
                e.insert(Func { pos, sz, args });
            },
            Entry::Vacant(e) => { e.insert(Func { pos, sz, args }); }
        }
        self.func_arg_syms.insert(name, arg_names);
    }

    pub fn sym_id(&mut self, name: &str) -> SymID {
        self.mem.symdb.put_ref(name).id()
    }

    pub fn sym(&mut self, name: &str) -> SymRef {
        self.mem.symdb.put_ref(name)
    }

    /**
     * Restore a breakpoint to its original instruction.
     *
     * # Arguments
     *
     * - `idx` : The position of the breakpoint in program memory.
     */
    pub fn unset_breakpoint(&mut self, idx: usize) -> Result<()> {
        self.pmem[idx] = self.breaks
                             .remove(&idx)
                             .ok_or_else(
                                 || RuntimeError::new(
                                     format!("No breakpoint at: {}", idx)))?;
        Ok(())
    }

    /**
     * Unwind the stack into a Traceback, if you don't need a Traceback you
     * should use `R8VM::unwind` instead. This method is far more expensive than
     * the non-traceback version.
     *
     * # Arguments
     *
     * - `ip` : The instruction IP from which to unwind.
     * - `err` : The error to initialize the Traceback with
     */
    pub fn unwind_traceback(&mut self, mut ip: usize, err: Error) -> Traceback {
        let mut pos_to_fn: Vec<(usize, SymID)> = Vec::new();
        for (name, func) in self.funcs.iter() {
            pos_to_fn.push((func.pos, *name));
        }
        pos_to_fn.sort_unstable();

        let get_name = |pos| {
            pos_to_fn[match pos_to_fn.binary_search_by(|s| s.0.cmp(&pos)) {
                Ok(idx) => idx,
                Err(idx) => ((idx as isize) - 1).max(0) as usize
            }].1
        };

        let mut frames = Vec::new();

        while ip != 0 {
            let mut name = get_name(ip);
            let func = self.funcs
                           .get(&name)
                           .expect("Unable to find function by binary search");

            let (nenv, nargs) = if func.pos + func.sz < ip {
                name = Builtin::Unknown.sym_id();
                (0, 0)
            } else {
                let spec = func.args;
                (spec.env as usize,
                 spec.sum_nargs() as usize)
            };

            let frame = self.frame;
            if frame >= self.mem.stack.len() || frame+nargs >= self.mem.stack.len() {
                log::warn!("Incomplete stack trace!");
                break;
            }
            let args = self.mem.stack.drain(frame..frame+nargs)
                                     .map(|v| v.to_string())
                                     .collect();
            let src = self.get_source(ip);
            frames.push(TraceFrame { args,
                                     func: OpName::OpSym(name.into()),
                                     src });

            self.mem.stack.drain(frame..frame+nenv).for_each(drop);
            if frame >= self.mem.stack.len() {
                log::warn!("Incomplete stack trace!");
                break;
            }
            ip = match self.mem.stack[frame] {
                PV::UInt(x) => x,
                _ => {
                    log::warn!("Incomplete stack trace!");
                    break;
                }
            };
            self.frame = match self.mem.stack[frame+1] {
                PV::UInt(x) => x,
                _ => {
                    log::warn!("Incomplete stack trace!");
                    break;
                }
            };
            self.mem.stack.drain(frame..).for_each(drop);
        }

        Traceback { frames, err }
    }

    // FIXME: This function is super slow, unoptimized, and only for debugging
    fn traceframe(&self, ip: usize) -> SymID {
        let mut pos_to_fn: Vec<(usize, SymID)> = Vec::new();
        for (name, func) in self.funcs.iter() {
            pos_to_fn.push((func.pos, *name));
        }
        pos_to_fn.sort_unstable();

        let get_name = |pos| {
            pos_to_fn[match pos_to_fn.binary_search_by(|s| s.0.cmp(&pos)) {
                Ok(idx) => idx,
                Err(idx) => ((idx as isize) - 1).max(0) as usize
            }].1
        };

        get_name(ip)
    }

    #[allow(dead_code)] // Used for internal debugging/profiling
    fn count_trace(&mut self, ip: usize) {
        let frame = self.traceframe(ip);
        let _v = match self.trace_counts.entry(frame) {
            Entry::Occupied(mut e) => {
                let v = *e.get();
                e.insert(v + 1)
            },
            Entry::Vacant(e) => { *e.insert(1) },
        };
    }

    pub fn count_trace_report(&self) {
        let mut xs: Vec<_> = self.trace_counts.iter().collect();
        xs.sort_unstable_by_key(|(_, v)| **v);
        for (k, v) in xs.into_iter() {
            println!("{k} ({v})");
        }
    }

    unsafe fn run_from_unwind(&mut self, offs: usize, pframe: usize, internal: bool)
                              -> std::result::Result<usize, Traceback>
    {
        self.catch();
        let res = match self.run_from(offs) {
            Ok(ip) => Ok(ip),
            Err((ip, e)) => {
                Err(self.unwind_traceback(ip, e))
            },
        };
        if !internal {
            self.mem.pop_borrows();
        }
        self.frame = pframe;
        self.catch_pop();
        res
    }

    #[inline]
    fn op_clzcall(&mut self,
                  ip: *mut r8c::Op,
                  nargs: u16) -> Result<*mut r8c::Op> {
        let idx = self.mem.stack.len() - nargs as usize - 1;
        let lambda_pv = self.mem.stack[idx];
        let err = move || err!(TypeNError,
                               expect: vec![Builtin::Lambda,
                                            Builtin::Subr,
                                            Builtin::Continuation,
                                            Builtin::Object],
                               got: lambda_pv.bt_type_of());
        let PV::Ref(p) = lambda_pv else { return err() };
        match unsafe { mem::transmute(((*p).meta.0 & META_TYPE_MASK) >> 2) } {
            NkT::Lambda => unsafe {
                let lambda = fastcast::<nkgc::Lambda>(p);
                (*lambda).args.check(nargs).map_err(|e| e.bop(Builtin::GreekLambda))?;
                let has_env = (*lambda).args.has_env();
                if !has_env {
                    self.mem.stack.drain(idx..(idx+1)).for_each(drop); // drain gang
                }
                self.call_pre(ip);
                self.frame = self.mem.stack.len()
                    - 2
                    - nargs as usize
                    - has_env as usize;
                Ok(self.ret_to((*lambda).pos))
            }
            NkT::Subroutine => unsafe {
                let subr = fastcast_mut::<Box<dyn Subr>>(p);
                // FIXME: This has been disabled pending a review, it is unsound
                //        for quite a few sysfn subrs.
                // SAFETY: The Subr trait is marked unsafe, read the associated
                //         safety documentation in Subr as to why this is safe. The
                //         alternative is to clone the stack slice, which is too
                //         expensive for us to do it for *every* Lisp->Rust call.
                //let args = unsafe {
                //    let delta = (self.mem.stack.len() - nargs as usize) as isize;
                //    let ptr = self.mem.stack.as_ptr().offset(delta);
                //    slice::from_raw_parts(ptr, nargs as usize)
                //};
                // FIXME: Avoid having to always clone
                let top = self.mem.stack.len();
                let args: Vec<_> = self.mem.stack[top - nargs as usize..].to_vec();

                let dip = self.ip_delta(ip);
                let res = (*subr).call(self, &args[..]).map_err(|e| {
                    let ipd = self.ip_delta(ip) - 1;
                    e.insert_traceframe(self.get_source(ipd),
                                        OpName::OpStr((*subr).name()),
                                        &args[..])
                });
                invalid!(args, subr); // (*subr).call
                self.mem.stack.drain(idx..).for_each(drop); // drain gang
                self.mem.push(res?);
                Ok(self.ret_to(dip))
            }
            NkT::Continuation => unsafe {
                let cont = fastcast::<Continuation>(p);
                ArgSpec::normal(1).check(nargs).map_err(|e| e.bop(Builtin::Continuation))?;
                let pv = self.mem.pop().unwrap();
                (*cont).inst(&mut self.mem.stack);
                self.mem.stack.push(pv);
                self.frame = (*cont).frame;
                Ok(self.ret_to((*cont).dip))
            }
            NkT::Object => unsafe {
                let s = fastcast_mut::<Object>(p);
                let top = self.mem.stack.len();
                let args: Vec<_> = self.mem.stack[top - nargs as usize..].to_vec();
                let dip = self.ip_delta(ip);
                let res = self.call_method(ip, s, &args[..]);
                self.mem.stack.drain(idx..).for_each(drop); // drain gang
                self.mem.push(res?);
                Ok(self.ret_to(dip))
            }
            _ => err()
        }
    }

    #[inline(never)]
    fn vcall(&mut self, mut ip: *mut r8c::Op, idx: u32, nargs: u16) -> Result<*mut r8c::Op> {
        let sym = self.mem.env[idx as usize].sym().unwrap();
        match self.funcs.get(&sym) {
            Some(func) => {
                func.args.check(nargs).map_err(|e| e.op(sym))?;
                let pos = func.pos;
                // FIXME: This does not pass in miri because of aliasing
                // (*ip.sub(1)) = CALL(pos as u32, nargs);
                self.call_pre(ip);
                self.frame = self.mem.stack.len() - 2 - (nargs as usize);
                ip = self.ret_to(pos);
            },
            None => if let Some(idx) = self.get_env_global(sym) {
                let var = self.mem.get_env(idx);
                let sidx = self.mem.stack.len() - nargs as usize;
                // FIXME: This can be made less clunky by modifying
                // op_clzcall so that it takes the callable as a parameter.
                self.mem.stack.insert(sidx, var);
                ip = self.op_clzcall(ip, nargs)?;
            } else {
                return Err(ErrorKind::UndefinedFunction {
                    name: sym.into()
                }.into())
            }
        };
        Ok(ip)
    }

    #[inline(never)]
    unsafe fn apl(&mut self, ip: *mut r8c::Op) -> Result<*mut r8c::Op> {
        let args = self.mem.pop().unwrap();
        let nargs = (|| -> Result<_> {
            match args {
                PV::Nil => return Ok(0),
                #[cfg(feature = "math")] PV::Vec2(w) => {
                    self.mem.push(PV::Real(w.x));
                    self.mem.push(PV::Real(w.y));
                    return Ok(2)
                }
                #[cfg(feature = "math")] PV::Vec3(w) => {
                    self.mem.push(PV::Real(w.x));
                    self.mem.push(PV::Real(w.y));
                    self.mem.push(PV::Real(w.z));
                    return Ok(3)
                }
                PV::Ref(p) => match to_fissile_mut(p) {
                    NkMut::Cons(_) => return
                        Ok(args.into_iter().map(|a| self.mem.push(a)).count()),
                    NkMut::Vector(xs) => return
                        Ok((*xs).iter().map(|a| self.mem.push(*a)).count()),
                    NkMut::Iter(it) => return
                        Ok((*it).by_ref().map(|a| self.mem.push(a)).count()),
                    _ => (),
                }
                _ => ()
            };
            err!(TypeNError,
                 expect: vec![Builtin::List, Builtin::Vector],
                 got: args.bt_type_of())
        })().map_err(|e| e.bop(Builtin::Apply))?;
        let nargs: u16 = match nargs.try_into() {
            Ok(n) => n,
            Err(e) => {
                self.mem.popn(nargs);
                self.mem.push(PV::Nil);
                return Err(e.into());
            }
        };
        self.op_clzcall(ip, nargs)
    }

    /**
     * Start running code from a point in program memory.
     *
     * NOTE: If the code isn't well-formed, i.e produces out-of-bounds jumps,
     * then you've yee'd your last haw.
     */
    unsafe fn run_from(&mut self, offs: usize) -> std::result::Result<usize, (usize, Error)> {
        let mut regs: Regs<2> = Regs::new();
        let mut ip = &mut self.pmem[offs] as *mut r8c::Op;
        use r8c::Op::*;
        macro_rules! op2 {
            ($r:ident, $op:ident, $rp:expr) => {{
                let len = self.mem.stack.len();
                let s = &self.mem.stack[len - 2..];
                let $r = s.get_unchecked(0).$op(&s.get_unchecked(1));
                self.mem.stack.truncate(len - 2);
                self.mem.stack.push($rp);
            }};
        }
        #[cfg(debug_assertions)]
        let mut orig = None;
        #[cfg(debug_assertions)]
        if self.debug_mode {
            let sym = self.traceframe(offs);
            orig = Some(sym);
            println!("{}:", sym);
        }
        let mut run = || loop {
            let op = *ip;
            ip = ip.offset(1);

            #[cfg(debug_assertions)]
            if self.debug_mode {
                match op {
                    VCALL(f, _) => println!("{}:", f),
                    CALL(ip, _) => {
                        let sym = self.traceframe(ip as usize);
                        println!("{}:", sym);
                    }
                    _ => ()
                }
                println!("  {}", op);
            }

            match op {
                // List processing
                CAR() => {
                    let it = self.mem.pop()?;
                    with_ref!(it, Cons(p) => {
                        self.mem.push((*p).car);
                        Ok(())
                    }).map_err(|e| e.bop(Builtin::Car))?
                },
                CDR() => {
                    let it = self.mem.pop()?;
                    with_ref!(it, Cons(p) => {
                        self.mem.push((*p).cdr);
                        Ok(())
                    }).map_err(|e| e.bop(Builtin::Cdr))?
                },
                LST(n) => {
                    self.mem.list(n)
                },
                VLT() => {
                    let len = self.mem.pop()?.force_int() as u32;
                    self.mem.list(len);
                }
                CNS() => self.mem.cons(),
                APN(n) => self.mem.append(n)?,

                // Iterators
                NXT(var) => {
                    let offset = (self.frame as isize) + (var as isize);
                    let it = *self.mem.stack.as_ptr().offset(offset);
                    with_ref_mut!(it, Iter(it) => {
                        let elem = (*it).next()
                                        .unwrap_or_else(
                                            || PV::Sym(Builtin::IterStop.sym_id()));
                        self.mem.push(elem);
                        Ok(())
                    }).map_err(|e| e.bop(Builtin::Next))?;
                }

                // Vectors
                VEC(n) => {
                    let len = self.mem.stack.len();
                    let vec = self.mem.stack
                                      .drain(len-(n as usize)..)
                                      .collect::<Vec<_>>();
                    let ptr = self.mem.put_pv(vec);
                    self.mem.push(ptr);
                }
                VPUSH() => {
                    let vec = self.mem.pop()?;
                    let elem = self.mem.pop()?;
                    with_ref_mut!(vec, Vector(v) => {
                        (*v).push(elem);
                        Ok(())
                    }).map_err(|e| e.bop(Builtin::Push))?
                }
                VPOP() => {
                    let vec = self.mem.pop()?;
                    with_ref_mut!(vec, Vector(v) => {
                        let elem = (*v).pop().unwrap_or(PV::Nil);
                        self.mem.push(elem);
                        Ok(())
                    }).map_err(|e| e.bop(Builtin::Pop))?;
                }
                VGET() => {
                    let idx = self.mem.pop()?;
                    let vec = self.mem.pop()?;
                    let err = || Error::new(ErrorKind::TypeNError {
                        expect: vec![Builtin::Vector,
                                     Builtin::Vec2,
                                     Builtin::Vec3],
                        got: vec.bt_type_of(),
                    });
                    #[cfg(feature = "math")]
                    let ierr = |x: PV| Err(error!(TypeError,
                                                  expect: Builtin::Integer,
                                                  got: x.bt_type_of()).bop(Builtin::Get).argn(2));
                    let elem = match (idx, vec) {
                        (idx, PV::Ref(p)) => match (idx, atom_kind(p)) {
                            (PV::Int(idx), NkT::Vector) =>
                                (*fastcast::<Vec<PV>>(p)).get(idx as usize).ok_or(error!(IndexError, idx: idx as usize)).copied(),
                            (PV::Ref(_), NkT::Table) => err!(KeyReference, key: idx.to_string()),
                            (idx, NkT::Table) =>
                                Ok((*fastcast::<FnvHashMap<PV, PV>>(p)).get(&idx).copied().unwrap_or_default()),
                            _ => Err(err())
                        }
                        #[cfg(feature = "math")] (PV::Int(0), PV::Vec2(glam::Vec2 { x, .. })) => Ok(PV::Real(x)),
                        #[cfg(feature = "math")] (PV::Int(1), PV::Vec2(glam::Vec2 { y, .. })) => Ok(PV::Real(y)),
                        #[cfg(feature = "math")] (PV::Int(x), PV::Vec2(_)) => err!(IndexError, idx: x as usize),
                        #[cfg(feature = "math")] (x, PV::Vec2(_)) => ierr(x),
                        #[cfg(feature = "math")] (PV::Int(0), PV::Vec3(glam::Vec3 { x, .. })) => Ok(PV::Real(x)),
                        #[cfg(feature = "math")] (PV::Int(1), PV::Vec3(glam::Vec3 { y, .. })) => Ok(PV::Real(y)),
                        #[cfg(feature = "math")] (PV::Int(2), PV::Vec3(glam::Vec3 { z, .. })) => Ok(PV::Real(z)),
                        #[cfg(feature = "math")] (PV::Int(x), PV::Vec3(_)) => err!(IndexError, idx: x as usize),
                        #[cfg(feature = "math")] (x, PV::Vec3(_)) => ierr(x),
                        _ => Err(err())
                    }.map_err(|e| e.bop(Builtin::Get))?;
                    self.mem.push(elem);
                }
                VSET() => {
                    // (set (get <vec> <idx>) <val>)
                    let len = self.mem.stack.len();
                    let args = &mut self.mem.stack[len - 3..];
                    with_ref_mut!(args[1], Vector(v) => {
                        TryInto::<usize>::try_into(args[2])
                            .map_err(|_| error!(TypeError,
                                                expect: Builtin::Integer,
                                                got: args[2].bt_type_of()).bop(Builtin::Set).argn(2))
                            .and_then(|idx| if idx >= (*v).len() {
                                err!(IndexError, idx)
                            } else {
                                *(*v).get_unchecked_mut(idx) = args[0];
                                Ok(())
                            })
                    }, Table(t) => {
                        if args[2].is_ref() {
                            err!(KeyReference, key: args[2].to_string())
                        } else {
                            (*t).insert(args[2], args[0]);
                            Ok(())
                        }
                    }).map_err(|e| e.bop(Builtin::Set))?;
                    self.mem.stack.truncate(len - 3);
                }
                LEN() => {
                    let li = self.mem.pop()?;
                    let len = with_ref!(li,
                                        Vector(v) => { Ok((*v).len()) },
                                        String(s) => { Ok((*s).len()) },
                                        Table(s) => { Ok((*s).len()) },
                                        Cons(_) => { Ok(li.iter().count()) })
                        .map_err(|e| e.bop(Builtin::Len))?;
                    self.mem.push(PV::Int(len as Int));
                }

                // Value creation
                NIL() => self.mem.push(PV::Nil),
                INS(idx) => {
                    let pv = self.mem.get_env(idx as usize).deep_clone(&mut self.mem)?;
                    self.mem.push(pv);
                },
                BOOL(i) => self.mem.push(PV::Bool(i != 0)),
                ZAV(nargs, nenv) => {
                    let start_idx = self.frame + nargs as usize;
                    let end_idx = start_idx + nenv as usize;
                    let lambda = self.mem.stack[self.frame];
                    let new_env = &self.mem.stack[start_idx..end_idx];
                    // Save environment
                    with_ref_mut!(lambda, Lambda(lambda) => {
                        for (dst, var) in (*lambda).locals.iter_mut().zip(new_env.iter()) {
                            *dst = *var;
                        }
                        Ok(())
                    })?;
                }
                ARGS(_nargs, _nopt, _env, _rest) => {}
                CLZ(pos, nenv) => {
                    let ipd = self.ip_delta(ip);
                    let ARGS(nargs, nopt, env, rest) = *self.pmem.get_unchecked(ipd-2) else {
                        panic!("CLZR without ARGSPEC");
                    };
                    let spec = ArgSpec { nargs, nopt, env, rest: rest == 1 };
                    let to = self.mem.stack.len();
                    let from = to - nenv as usize;
                    let locals = self.mem.stack.drain(from..to).collect();
                    self.mem.push_new(nkgc::Lambda { pos: pos as usize,
                                                     args: spec,
                                                     locals });
                }

                // Math
                ADD() => op2!(r, add, r?),
                SUB() => op2!(r, sub, r?),
                DIV() => op2!(r, div, r?),
                MUL() => op2!(r, mul, r?),

                ADS(dst, src) => {
                    let o = *self.mem.stack.get_unchecked(self.frame + (src as usize));
                    self.mem.stack.get_unchecked_mut(self.frame + (dst as usize)).add_mut(&o)?;
                }
                SUS(dst, src) => {
                    let o = *self.mem.stack.get_unchecked(self.frame + (src as usize));
                    self.mem.stack.get_unchecked_mut(self.frame + (dst as usize)).sub_mut(&o)?;
                }
                INC(v, d) => match self.mem.stack.get_unchecked_mut(self.frame + (v as usize)) {
                    PV::Int(ref mut x) => *x += d as Int,
                    PV::Real(ref mut x) => *x += f32::from(d),
                    x => return Err(RuntimeError::new(format!("Cannot increment: {}", x)).into()),
                },
                DEC(v, d) => match self.mem.stack.get_unchecked_mut(self.frame + (v as usize)) {
                    PV::Int(ref mut x) => *x -= d as Int,
                    PV::Real(ref mut x) => *x -= f32::from(d),
                    x => return Err(RuntimeError::new(format!("Cannot decrement: {}", x)).into()),
                },

                // Logic
                EQL() => op2!(r, eq, r.into()),
                EQP() => op2!(r, equalp, r.into()),
                GT() => op2!(r, gt, r?),
                GTE() => op2!(r, gte, r?),
                LT() => op2!(r, lt, r?),
                LTE() => op2!(r, lte, r?),
                NOT() => {
                    let v = !bool::from(self.mem.pop()?);
                    self.mem.push(PV::Bool(v));
                },

                // Flow control
                JMP(d) => ip = ip.offset(d as isize - 1),
                JT(d) => if bool::from(self.mem.pop()?) {
                    ip = ip.offset(d as isize - 1);
                }
                JN(d) => if !bool::from(self.mem.pop()?) {
                    ip = ip.offset(d as isize - 1);
                }
                JZ(d) => if self.mem.stack.pop() == Some(PV::Int(0)) {
                    ip = ip.offset(d as isize - 1);
                }
                JNZ(d) => if self.mem.stack.pop() != Some(PV::Int(0)) {
                    ip = ip.offset(d as isize - 1);
                }
                JV(mul, max) => {
                    let n = self.mem.pop()?.force_int();
                    let d = cmp::min((mul as isize) * n, max as isize);
                    ip = ip.offset(d);
                }
                VCALL(idx, nargs) => ip = self.vcall(ip, idx, nargs)?,
                CALL(pos, nargs) => {
                    self.call_pre(ip);
                    self.frame = self.mem.stack.len() - 2 - (nargs as usize);
                    ip = self.ret_to(pos as usize);
                }
                RET() => {
                    let rv = self.mem.pop()?;
                    let old_frame = self.frame;
                    if let PV::UInt(frame) = self.mem.pop()? {
                        self.frame = frame;
                    }
                    if let PV::UInt(delta) = self.mem.pop()? {
                        ip = self.ret_to(delta);
                    }
                    // yeet the stack frame
                    self.mem.stack.truncate(old_frame);
                    self.mem.push(rv);
                }
                ZCALL(nargs) => ip = self.op_clzcall(ip, nargs)?,
                APL() => ip = self.apl(ip)?,
                CCONT(dip) => {
                    let dip = self.ip_delta(ip) as isize + dip as isize;
                    let mut stack_dup = self.mem.stack.clone();
                    stack_dup.pop();
                    let cnt = self.mem.put_pv(
                        Continuation::new(stack_dup, self.frame, dip as usize));
                    self.mem.push(cnt);
                    ip = self.op_clzcall(ip, 1)?;
                }
                UWND() => {
                    self.unwind();
                    return Ok(())
                }

                // Stack manipulation
                MOV(var) => {
                    let offset = (self.frame as isize) + (var as isize);
                    self.mem
                        .push(*self.mem.stack.as_ptr().offset(offset))
                }
                STR(var) => {
                    let offset = (self.frame as isize) + (var as isize);
                    *(self.mem.stack.as_mut_ptr().offset(offset)) = self.mem.pop()?
                },
                POP(n) => self.mem.popn(n as usize),
                POPA(keep, pop) => {
                    let keep = keep as usize;
                    let pop = pop as usize;
                    let st = &mut self.mem.stack;
                    let top = st.len();
                    for (hi, lo) in (top - keep..top).zip(top - pop - keep..top) {
                        st[lo] = st[hi];
                    }
                    st.truncate(top - pop);
                }
                INT(n) => self.mem.push(PV::Int(n as Int)),
                FLT(n) => self.mem.push(PV::Real(f32::from_bits(n))),
                CHR(c) => self.mem.push(PV::Char(char::from_u32_unchecked(c))),
                SAV(num) => regs.save(&mut self.mem, num)?,
                RST() => regs.restore(&mut self.mem),
                TOP(d) => {
                    let top = self.mem.stack.len() - self.frame;
                    self.mem.push(PV::Int((top as Int) - (d as Int)));
                }
                DUP() => self.mem.dup()?,
                ZXP() => self.mem.clz_expand(self.frame)?,

                // Static/env variables
                GET(var) => {
                    let val = self.mem.get_env(var as usize);
                    self.mem.push(val);
                },
                SET(var) => {
                    let val = self.mem.pop()?;
                    self.mem.set_env(var as usize, val);
                }

                HCF() => {
                    #[cfg(debug_assertions)]
                    if self.debug_mode {
                        println!("hcf from {:?}", orig);
                    }
                    return Ok(())
                },
            }
            #[cfg(debug_assertions)]
            if self.debug_mode { self.dump_stack().unwrap(); }
            self.mem.collect();
        };

        let res = run();
        let dip = self.ip_delta(ip);
        match res {
            Ok(_) => Ok(dip),
            Err(e) => {
                let er: Error = e;
                Err((dip, er.src(self.get_source(dip))))
            }
        }
    }

    pub fn dump_stack(&mut self) -> Result<()> {
        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "stack:")?;
        if self.mem.stack.is_empty() {
            writeln!(stdout, "    (empty)")?;
        }
        for (idx, val) in self.mem.stack.iter().enumerate().rev() {
            let (idx, frame) = (idx as i64, self.frame as i64);
            write!(stdout, "{}", if idx == frame { " -> " } else { "    " })?;
            writeln!(stdout, "{}: {}", idx - frame, val.lisp_to_string())?;
        }
        Ok(())
    }

    #[inline]
    fn ret_to(&mut self, dip: usize) -> *mut r8c::Op {
        &mut self.pmem[dip] as *mut r8c::Op
    }

    #[inline]
    fn ip_delta(&mut self, ip: *const r8c::Op) -> usize {
        (ip as usize - self.ret_to(0) as usize) / mem::size_of::<r8c::Op>()
    }

    #[inline]
    fn call_pre(&mut self, ip: *const r8c::Op) {
        let dip = self.ip_delta(ip);
        self.mem.push(PV::UInt(dip));
        self.mem.push(PV::UInt(self.frame));
    }

    /**
     * Call a function, returning either the return value of
     * the function or an error.
     *
     * # Arguments
     *
     * - `sym` : Symbol mapped to the function, see Arena::sym.
     * - `args` : Arguments that should be passed.
     */
    pub fn call(&mut self, sym: SymID, args: impl AsArgs) -> Result<PV> {
        Ok(symcall_with!(self, sym, args.inner_nargs(), {
            args.inner_pusharg(&mut self.mem)?
        }))
    }

    pub fn ncall<A>(&mut self, sym: SymID, args: impl NArgs<A>) -> Result<PV> {
        Ok(symcall_with!(self, sym, args.nargs(), {
            args.pusharg(&mut self.mem)?
        }))
    }

    pub fn callfn<A>(&mut self, funk: &Func, args: impl NArgs<A>) -> Result<PV> {
        let pos = funk.pos;
        funk.args.check(args.nargs() as u16)?;
        Ok(call_with!(self, pos, args.nargs(), {
            args.pusharg(&mut self.mem)?
        }))
    }

    pub fn call_spv(&mut self, sym: SymID, args: impl AsArgs) -> Result<SPV> {
        let res = self.call(sym, args)?;
        Ok(self.mem.make_extref(res))
    }

    pub fn napply_pv<A>(&mut self, f: PV, args: impl NArgs<A>) -> Result<PV> {
        let frame = self.frame;
        self.frame = self.mem.stack.len();
        self.mem.push(PV::UInt(0));
        self.mem.push(PV::UInt(frame));
        self.mem.push(f);
        let pos = clzcall_pad_dip(args.nargs() as u16);
        args.pusharg(&mut self.mem)?;
        unsafe {
            self.run_from_unwind(pos, frame, false)?;
        }
        self.mem.pop()
    }

    pub fn apply_spv(&mut self, f: SPV, args: impl AsArgs) -> Result<PV> {
        let frame = self.frame;
        self.frame = self.mem.stack.len();
        self.mem.push(PV::UInt(0));
        self.mem.push(PV::UInt(frame));
        self.mem.push(f.pv(&self.mem));
        let pos = clzcall_pad_dip(args.inner_nargs() as u16);
        args.inner_pusharg(&mut self.mem)?;
        unsafe {
            self.run_from_unwind(pos, frame, false)?;
        }
        self.mem.pop()
    }

    pub fn eval_pv(&mut self, ast: PV) -> Result<PV> {
        self.macroexpand_pv(ast, false).and_then(|ast| {
            let excv = Excavator::new(&self.mem);
            let mut ast = excv.to_ast(ast, Source::none())?;
            let mut opto = Optomat::new();
            opto.visit(&mut ast)?;
            let mut cc = R8Compiler::new(self);
            let modfn_pos = cc.compile_top_tail(ast)?;
            cc.take(self)?;
            Ok(call_with!(self, modfn_pos, 0, {}))
        })
    }

    pub fn print_fmt(&mut self, args: fmt::Arguments) -> Result<()> {
        self.stdout.lock().unwrap().write_fmt(args)?;
        Ok(())
    }

    pub fn println_fmt(&mut self, args: fmt::Arguments) -> Result<()> {
        let mut out = self.stdout.lock().unwrap();
        out.write_fmt(args)?;
        out.write_all(b"\n")?;
        Ok(())
    }

    pub fn print(&mut self, obj: &dyn Display) -> Result<()> {
        self.print_fmt(format_args!("{}", obj))
    }

    pub fn println(&mut self, obj: &dyn Display) -> Result<()> {
        self.print(obj)?;
        writeln!(self.stdout.lock().unwrap())?;
        Ok(())
    }

    pub fn flush_output(&mut self) -> Result<()> {
        self.stdout.lock().unwrap().flush().map_err(|e| e.into())
    }

    pub fn set_stdout(&mut self, out: Box<dyn OutStream>) {
        *self.stdout.lock().unwrap() = out;
    }

    pub fn dump_all_fns(&self) -> Result<()> {
        let mut funks = self.funcs.iter().map(|(k, v)| (k, v.pos)).collect::<Vec<_>>();
        funks.sort_by_key(|(_, v)| *v);
        for funk in funks.into_iter().map(|(u, _)| u) {
            self.dump_fn_code(*funk)?
        }
        Ok(())
    }

    pub fn dump_code(&self) -> Result<()> {
        for (i, op) in self.pmem.iter().enumerate() {
            println!("{i:0>8}    {op} {}", self.get_source(i))
        }
        Ok(())
    }

    pub fn dump_fn_code(&self, mut name: SymID) -> Result<()> {
        if let Some(mac_fn) = self.macros.get(&name) {
            name = *mac_fn;
        }
        let func = self.funcs.get(&name).ok_or("No such function")?;
        let start = func.pos as isize;

        let get_jmp = |op: r8c::Op| {
            use r8c::Op::*;
            Some(match op {
                JMP(d) => d,
                JT(d) => d,
                JN(d) => d,
                JZ(d) => d,
                JNZ(d) => d,
                _ => return None,
            }).map(|v| v as isize)
        };

        let fmt_special = |pos: isize, op: r8c::Op| {
            use r8c::Op::*;
            if let Some(delta) = get_jmp(op) {
                return Some((op.name().to_ascii_lowercase(),
                             vec![self.labels.get(&((pos + delta) as u32))
                                  .map(|lbl| format!("{}", lbl))
                                  .unwrap_or(format!("{}", delta))
                                  .style_asm_label_ref()
                                  .to_string()]))
            }
            Some((op.name().to_ascii_lowercase(), match op {
                VCALL(idx, args) => vec![self.mem.get_env(idx as usize).to_string(),
                                         args.to_string()],
                INS(idx) => vec![self.mem.get_env(idx as usize).to_string()],
                _ => return None
            }))
        };

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}({}):",
                 name.as_ref().style_asm_fn(),
                 func.args)?;
        for i in start..start+(func.sz as isize) {
            let op = self.pmem[i as usize];
            if let Some(s) = self.labels.get(&(i as u32)) {
                writeln!(stdout, "{}:", s.style_asm_label())?;
            }
            let (name, args) = fmt_special(i, op).unwrap_or(
                (op.name().to_ascii_lowercase(),
                 op.args().iter().map(|v| v.to_string()).collect())
            );
            writeln!(stdout, "    {} {} {}",
                     name.style_asm_op(),
                     args.join(", "),
                     self.get_source(i as usize))?;
        }

        Ok(())
    }

    #[cfg(feature = "extra")]
    pub fn dump_macro_tbl(&self) -> Result<()> {
        let mut table = Table::new();

        table.load_preset(TABLE_STYLE);
        table.set_header(vec!["Macro", "Function"]);
        for (&macro_sym, &fn_sym) in self.macros.iter() {
            table.add_row(vec![macro_sym.as_ref(), fn_sym.as_ref()]);
        }

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}", table)?;

        Ok(())
    }

    #[cfg(feature = "extra")]
    pub fn dump_symbol_tbl(&self) -> Result<()> {
        let mut table = Table::new();

        table.load_preset(TABLE_STYLE);
        table.set_header(vec!["Symbol", "ID"]);
        for (id, name) in self.mem.symdb.iter() {
            table.add_row(vec![name, &format!("{:?}", id)]);
        }

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}", table)?;

        Ok(())
    }

    #[cfg(feature = "extra")]
    pub fn dump_env_tbl(&self) -> Result<()> {
        let mut table = Table::new();

        table.load_preset(TABLE_STYLE);
        table.set_header(vec!["Symbol", "Value", "Index"]);
        for (&sym, &idx) in self.globals.iter() {
            table.add_row(vec![sym.as_ref(),
                               &self.mem.get_env(idx).lisp_to_string(),
                               &idx.to_string()]);
        }

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}", table)?;

        Ok(())
    }

    pub fn get_funcs_with_prefix(&self, prefix: &str) -> Vec<SymID> {
        let mut funcs = Vec::new();
        for (&sym, _) in self.funcs.iter() {
            if sym.as_ref().starts_with(prefix) {
                funcs.push(sym)
            }
        }
        funcs
    }

    pub fn code_sz(&self) -> usize {
        self.pmem.len() * std::mem::size_of::<r8c::Op>()
    }

    #[cfg(feature = "extra")]
    pub fn dump_fn_tbl(&self) -> Result<()> {
        let mut table = Table::new();

        table.load_preset(TABLE_STYLE);
        table.set_header(vec!["Name", "Nargs", "Position"]);
        for (&sym, func) in self.funcs.iter() {
            table.add_row(vec![sym.as_ref(),
                               &func.args.to_string(),
                               &func.pos.to_string()]);
        }

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}", table)?;

        Ok(())
    }

    pub fn pmem(&self) -> &Vec<r8c::Op> {
        &self.pmem
    }

    #[cfg(feature = "modules")]
    pub fn freeze(&self) -> LispModule {
        let mut exports = Vec::new();
        exports.extend(self.funcs.iter()
                       .map(|(&name, f)| Export::new(ExportKind::Func,
                                                     name,
                                                     f.pos.try_into().unwrap())));
        LispModule::new(&self.pmem, &self.mem.symdb, vec![], exports)
    }
}
