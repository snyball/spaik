//! SPAIK R8 Virtual Machine

#[cfg(feature = "extra")]
use comfy_table::Table;

#[cfg(feature = "modules")]
use crate::module::{LispModule, Export, ExportKind};
use crate::{
    ast::Excavator,
    chasm::{ASMOp, ChASMOpName, Lbl, ASMPV},
    compile::{Builtin, SourceList},
    error::{Error, ErrorKind, Source, OpName, Meta, LineCol, SourceFileName, Result},
    fmt::LispFmt,
    nuke::*,
    nkgc::{Arena, Cons, SymID, SymIDInt, PV, SPV, self, QuasiMut, Int},
    sexpr_parse::{sexpr_modifier_bt, string_parse, tokenize, Fragment, standard_lisp_tok_tree},
    subrs::{IntoLisp, Subr, IntoSubr, FromLisp},
    sym_db::SymDB, FmtErr, tok::Token, limits, comp::R8Compiler,
    stylize::Stylize, chasm::LblMap,
};
use fnv::FnvHashMap;
use std::{io, fs, borrow::Cow, cmp, collections::hash_map::Entry, convert::TryInto, fmt::{self, Debug, Display}, io::prelude::*, mem::{self, replace, take}, ptr::addr_of_mut, sync::Mutex, path::Path};

chasm_def! {
    r8c:

    // List processing
    CONS(),
    APPEND(num: u32),
    LIST(num: u32),
    VLIST(),
    CAR(),
    CDR(),
    // SETCAR(),
    // SETCDR(),

    // Iterators
    NXIT(var_idx: u16),

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
    // JSYM(dip: i32, sym: SymIDInt),
    // JNSYM(dip: i32, sym: SymIDInt),
    CALL(pos: u32, nargs: u16),
    VCALL(func: SymIDInt, nargs: u16),
    APL(),
    CLZCALL(nargs: u16),
    RET(),
    CALLCC(dip: i32),
    UNWIND(),
    HCF(),

    // Stack operations
    CONSTREF(idx: u32),
    INST(idx: u32),
    POP(num: u8),
    POPA(num_top: u16, num_pop: u16),
    SAV(num: u8),
    RST(),
    TOP(delta: u16),
    DUP(),
    CLZEXP(),
    // Stack variables
    MOV(var_idx: u16),
    STR(var_idx: u16),
    // Persistent variables
    GET(env_idx: u16),
    SET(env_idx: u16),

    // Value creation
    PUSH(val: i32),
    PUSHF(val: u32),
    ARGSPEC(nargs: u16, nopt: u16, nenv: u16, rest: u8),
    SYM(id: SymIDInt),
    CHAR(c: u32),
    CLZR(delta: i32, nenv: u16),
    CLZAV(nargs: u16, nenv: u16), // Commit the closure environment
    BOOL(val: u8),
    NIL(),

    // Logic
    EQL(),
    EQLP(),
    GT(),
    GTE(),
    LT(),
    LTE(),
    NOT(),

    // Math
    INC(var: u16, amount: u16),
    DEC(var: u16, amount: u16),
    ADD(),
    SUB(),
    DIV(),
    MUL()
}

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
    pub func: SymID,
    pub args: Vec<PV>,
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

fn tostring(vm: &R8VM, x: PV) -> String {
    match x {
        PV::Ref(y) => match to_fissile_ref(y) {
            NkRef::String(s) => unsafe { (*s).clone() },
            _ => x.lisp_to_string(&vm.mem),
        },
        PV::Char(c) => format!("{c}"),
        _ => x.lisp_to_string(&vm.mem),
    }
}

macro_rules! featurefn {
    ($ft:expr, $e:expr) => {{
        #[cfg(feature = $ft)]
        let funk = || -> Result<()> {
            $e;
            Ok(())
        };
        #[cfg(not(feature = $ft))]
        let funk = || -> Result<()> {
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
                     .op($vm.sym_id($self.name())))
        }
    };
}

macro_rules! std_subrs {
    ($(fn $name:ident($($inner:tt)*) -> Result<PV> $body:block)*) => {
        $(subr!(fn $name($($inner)*) -> Result<PV> $body);)*
    };
}

#[allow(non_camel_case_types)]
mod sysfns {
    use std::{fmt::Write, borrow::Cow};

    use crate::{subrs::{Subr, IntoLisp}, nkgc::PV, error::{Error, ErrorKind, Result}, fmt::{LispFmt, FmtWrap}, compile::Builtin, utils::Success};
    use super::{R8VM, tostring, ArgSpec};

    fn join_str<IT, S>(vm: &R8VM, args: IT, sep: S) -> String
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
                    _ => write!(&mut out, "{}", FmtWrap { val: &val,
                                                          db: vm }).unwrap(),
                }
                Ok(())
            }).unwrap();
        }
        out
    }

    std_subrs! {
        fn println(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            let s = tostring(vm, *x);
            vm.println(&s)?;
            Ok(*x)
        }

        fn sys_freeze(&mut self, vm: &mut R8VM, args: (_dst)) -> Result<PV> {
            featurefn!("modules", {
                let module = vm.freeze();
                let file = std::fs::File::create(_dst.str().as_ref())?;
                let mut wr = std::io::BufWriter::new(file);
                bincode::serialize_into(&mut wr, &module).unwrap();
            })?;
            Ok(PV::Nil)
        }

        fn print(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            let s = tostring(vm, *x);
            vm.print(&s)?;
            Ok(*x)
        }

        fn string(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            x.lisp_to_string(&vm.mem)
             .into_pv(&mut vm.mem)
        }

        fn eval(&mut self, vm: &mut R8VM, args: (ast)) -> Result<PV> {
            vm.eval_pv(*ast)
        }

        fn read(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            vm.read(&tostring(vm, *x))?;
            vm.mem.pop()
        }

        fn concat(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
            join_str(vm, args.iter().copied(), "").into_pv(&mut vm.mem)
        }

        fn error(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            if let PV::Sym(name) = *x {
                err!(LibError, name)
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
                                     Cow::from(vm.sym_name(*s))),
                [xs, o] => (xs.make_iter().map_err(emap)?, with_ref!(*o, String(s) => {
                    Ok(Cow::from(&(*s)[..]))
                }).map_err(|e| e.bop(Builtin::Join).argn(2))?),
                [xs] => (xs.make_iter()?, Cow::from("")),
                _ => return Err(error!(ArgError,
                                       expect: ArgSpec::opt(1, 1),
                                       got_num: args.len() as u32)
                                .bop(Builtin::Join))
            };
            join_str(vm, it, sep).into_pv(&mut vm.mem)
        }

        fn iter(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV> {
            x.make_iter().map_err(|e| e.argn(1))?.into_pv(&mut vm.mem)
        }

        fn exit(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV> {
            let status = args.first().copied()
                                     .unwrap_or_else(
                                         || PV::Sym(Builtin::KwOk.sym()));
            Err(Error::new(ErrorKind::Exit {
                status: status.try_into()
                              .map_err(|e: Error| e.argn(1).bop(Builtin::Exit))?
            }))
        }

        fn instant(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
            #[cfg(not(target_arch = "wasm32"))]
            return Ok(PV::Real(vm.mem.stats().time.as_secs_f32()));
            #[cfg(target_arch = "wasm32")]
            return Ok(PV::Nil);
        }

        fn dump_macro_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
            featurefn!("extra", vm.dump_macro_tbl()?)?;
            Ok(PV::Nil)
        }

        fn dump_sym_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
            featurefn!("extra", vm.dump_symbol_tbl()?)?;
            Ok(PV::Nil)
        }

        fn dump_env_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
            featurefn!("extra", vm.dump_env_tbl()?)?;
            Ok(PV::Nil)
        }

        fn dump_fn_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV> {
            featurefn!("extra", vm.dump_fn_tbl()?)?;
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

        fn load(&mut self, vm: &mut R8VM, args: (lib)) -> Result<PV> {
            Ok(PV::Sym(vm.load((*lib).try_into()?)?))
        }

        fn pow(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
            x.pow(y)
        }

        fn modulo(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV> {
            x.modulo(y)
        }

        fn set_macro(&mut self, vm: &mut R8VM, args: (macro_name, fn_name)) -> Result<PV> {
            vm.set_macro((*macro_name).try_into()?,
                         (*fn_name).try_into()?);
            Ok(PV::Nil)
        }

        fn set_macro_character(&mut self, vm: &mut R8VM, args: (macro_name, fn_name)) -> Result<PV> {
            vm.set_macro_character((*macro_name).try_into()?,
                                   (*fn_name).try_into()?);
            Ok(PV::Nil)
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct make_symbol;

    unsafe impl Subr for make_symbol {
        fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV> {
            match args {
                [s @ PV::Sym(_)] => Ok(*s),
                [r] => with_ref!(*r, String(s) => {
                    Ok(PV::Sym(vm.mem.symdb.put_ref(&*s)))
                }),
                _ => Err(error!(ArgError,
                                expect: ArgSpec::normal(1),
                                got_num: args.len() as u32)
                         .bop(Builtin::MakeSymbol))
            }
        }
        fn name(&self) -> &'static str { "make-symbol" }
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
                [PV::Sym(id)] => Ok(PV::Int((*id).try_into()?)),
                [x] => Err(error!(TypeError,
                                  expect: Builtin::Symbol,
                                  got: x.bt_type_of(),)
                           .bop(Builtin::SymID)
                           .argn(1)),
                _ => ArgSpec::normal(1).check(Builtin::SymID.sym(), args.len() as u16)
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

    pub fn check(&self, fn_sym: SymID, nargs: u16) -> Result<()> {
        if self.is_valid_num(nargs) {
            Ok(())
        } else {
            Err(error!(ArgError,
                       expect: *self,
                       got_num: nargs.into())
                .op(fn_sym))
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Func {
    pub pos: usize,
    pub sz: usize,
    pub args: ArgSpec,
}

impl Func {
    pub fn adjust(&mut self, pos: usize) {
        self.pos -= pos;
    }
}

pub trait OutStream: io::Write + Debug + Send {}
impl<T> OutStream for T where T: io::Write + Debug + Send {}

pub trait InStream: io::Read + Debug + Send {}
impl<T> InStream for T where T: io::Read + Debug + Send {}

#[derive(Debug)]
pub struct R8VM {
    /// Memory
    pub(crate) pmem: Vec<r8c::Op>,
    consts: Vec<NkSum>,
    pub(crate) mem: Arena,
    pub(crate) globals: FnvHashMap<SymID, usize>,
    pub(crate) trace_counts: FnvHashMap<SymID, usize>,
    tok_tree: Fragment,
    reader_macros: FnvHashMap<String, SymID>,

    // Named locations/objects
    breaks: FnvHashMap<usize, r8c::Op>,
    macros: FnvHashMap<SymIDInt, SymID>,
    pub(crate) funcs: FnvHashMap<SymIDInt, Func>,
    func_labels: FnvHashMap<SymID, FnvHashMap<u32, Lbl>>,
    pub(crate) labels: LblMap,
    func_arg_syms: FnvHashMap<SymID, Vec<SymID>>,
    pub(crate) srctbl: SourceList,
    catch: Vec<usize>,

    stdout: Mutex<Box<dyn OutStream>>,
    stdin: Mutex<Box<dyn InStream>>,

    debug_mode: bool,

    frame: usize,
}

impl Default for R8VM {
    fn default() -> Self {
        R8VM {
            pmem: Default::default(),
            reader_macros: Default::default(),
            tok_tree: standard_lisp_tok_tree(),
            consts: Default::default(),
            catch: Default::default(),
            mem: Default::default(),
            globals: Default::default(),
            breaks: Default::default(),
            macros: Default::default(),
            funcs: Default::default(),
            func_labels: Default::default(),
            func_arg_syms: Default::default(),
            stdout: Mutex::new(Box::new(io::stdout())),
            stdin: Mutex::new(Box::new(io::stdin())),
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
            $vm.run_from_unwind($pos)?;
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
        func.args.check($func.into(), $nargs.try_into().unwrap())?;

        let frame = $vm.frame;

        $vm.frame = $vm.mem.stack.len();
        $body
        $vm.mem.push(PV::UInt(0));
        $vm.mem.push(PV::UInt(frame));
        let pos = func.pos;
        unsafe {
            $vm.run_from_unwind(pos)?;
        }
        let res = $vm.mem.pop().expect(
            "Function did not return a value"
        );

        res
    }};
}

impl SymDB for R8VM {
    fn name(&self, sym: SymID) -> Cow<str> {
        (&self.mem.symdb as &dyn SymDB).name(sym)
    }

    fn put_sym(&mut self, name: &str) -> SymID {
        self.mem.symdb.put_ref(name)
    }
}

pub trait EnumCall {
    fn name(&self, mem: &mut Arena) -> SymID;
    fn pushargs(self, args: &[SymID], mem: &mut Arena) -> Result<()>;
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
        impl<$($arg),*> Args for ($($arg),*,)
            where $($arg: crate::subrs::IntoLisp + crate::subrs::RefIntoLisp ),*
        {
            fn pusharg(self, mem: &mut Arena) -> Result<()> {
                #[allow(non_snake_case)]
                let ($($arg),*,) = self;
                $(#[allow(non_snake_case)]
                  let $arg = $arg.into_pv(mem)?;
                  mem.push($arg);)*
                Ok(())
            }

            fn pusharg_ref(&self, mem: &mut Arena) -> Result<()> {
                #[allow(non_snake_case)]
                let ($($arg),*,) = self;
                $(#[allow(non_snake_case)]
                  let $arg = $arg.ref_into_pv(mem)?;
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

unsafe impl Send for R8VM {}

// NOTE: This only applies to calls made with apply_spv, calls internally in the
// VM bytecode are unbounded.
const MAX_CLZCALL_ARGS: u16 = 12;

#[inline]
const fn clzcall_pad_dip(nargs: u16) -> usize {
    debug_assert!(nargs <= MAX_CLZCALL_ARGS);
    // NOTE: See R8VM::new, it creates a MAX_CLZCALL_ARGS number of
    // CLZCALL(n)/RET bytecodes after the first HCF bytecode.
    1 | (nargs as usize) << 1
}

impl R8VM {
    pub fn no_std() -> R8VM {
        let mut vm = R8VM {
            pmem: vec![r8c::Op::HCF()],
            ..Default::default()
        };

        for i in 0..=MAX_CLZCALL_ARGS {
            let pos = vm.pmem.len();
            vm.pmem.push(r8c::Op::CLZCALL(i));
            vm.pmem.push(r8c::Op::RET());
            let sym = vm.mem.symdb.put(format!("<ζ>::clz-entrypoint-{i}"));
            vm.funcs.insert(sym.into(), Func {
                pos,
                sz: 2,
                args: ArgSpec::normal(0)
            });
        }

        vm.funcs.insert(Builtin::HaltFunc.sym().into(), Func {
            pos: 0,
            sz: 1,
            args: ArgSpec::none()
        });

        macro_rules! addfn {
            ($name:ident) => {
                addfn!(stringify!($name), $name);
            };

            ($name:expr, $fn:ident) => {
                let sym = vm.mem.put_sym($name);
                vm.set(sym, (sysfns::$fn).into_subr()).unwrap();
            };
        }

        // IO
        addfn!(println);
        addfn!(print);
        addfn!(instant);

        // Modules
        addfn!(load);

        // Meta
        addfn!(eval);
        addfn!(read);
        addfn!(macroexpand);
        addfn!("make-symbol", make_symbol);
        addfn!("sys/freeze", sys_freeze);
        addfn!("read-compile", read_compile);
        addfn!("read-compile-from", read_compile_from);
        addfn!("type-of", type_of);
        addfn!("sym-id", sym_id);
        addfn!("sys/set-macro", set_macro);
        addfn!("sys/set-macro-character", set_macro_character);

        // Debug
        addfn!("dump-fns", dump_all_fns);
        addfn!("dump-code", dump_code);
        addfn!("dump-macro-tbl", dump_macro_tbl);
        addfn!("dump-sym-tbl", dump_sym_tbl);
        addfn!("dump-env-tbl", dump_env_tbl);
        addfn!("dump-fn-tbl", dump_fn_tbl);
        addfn!("dump-gc-stats", dump_gc_stats);
        addfn!("dump-stack", dump_stack);
        addfn!(disassemble);

        // Control-Flow
        addfn!(error);
        addfn!(exit);

        // Arithmetic
        addfn!("%", modulo);
        addfn!("+", sum);
        addfn!("-", asum);
        addfn!("*", product);
        addfn!("/", aproduct);
        addfn!(pow);

        // Strings
        addfn!(string);
        addfn!(concat);
        addfn!(join);

        // Iter
        addfn!(iter);

        let src = Some(Cow::Borrowed("<ζ>::boot-stage0"));
        vm.read_compile(include_str!("../lisp/boot-stage0.lisp"),
                        src.clone()).unwrap();

        vm
    }

    pub fn new() -> R8VM {
        let mut vm = R8VM::no_std();

        let src = Some(Cow::Borrowed("<ζ>::core"));
        let core = include_str!("../lisp/core.lisp");
        vm.read_compile(core, src).fmt_unwrap(&vm);

        vm
    }

    pub fn has_mut_extrefs(&self) -> bool {
        self.mem.has_mut_extrefs()
    }

    pub fn call_by_enum(&mut self, enm: impl EnumCall) -> Result<PV> {
        let name = enm.name(&mut self.mem);
        let args = self.func_arg_syms.get(&name).map(|v| &**v).ok_or(
            error!(UndefinedFunction, name)
        )?;
        let nargs = args.len();
        Ok(symcall_with!(self, name, nargs, { enm.pushargs(args, &mut self.mem)? }))
    }

    pub fn minimize(&mut self) {
        self.mem.minimize();
        self.pmem.shrink_to_fit();
        self.consts.shrink_to_fit();
        self.globals.shrink_to_fit();
        self.breaks.shrink_to_fit();
        self.funcs.shrink_to_fit();
        self.func_labels.shrink_to_fit();
    }

    pub fn set<T: IntoLisp>(&mut self, var: SymID, obj: T) -> Result<()> {
        let pv = obj.into_pv(&mut self.mem)?;
        let idx = self.mem.push_env(pv);
        self.globals.insert(var, idx);
        Ok(())
    }

    pub fn add_subr(&mut self, subr: impl Subr) {
        let name = self.put_sym(subr.name());
        self.set(name, subr.into_subr())
            .expect("Can't allocate Subr");
    }

    pub fn set_subr(&mut self, _name: SymID, _obj: Box<dyn Subr>) {
        todo!()
    }

    pub fn set_debug_mode(&mut self, debug_mode: bool) {
        self.debug_mode = debug_mode;
    }

    pub fn get_debug_mode(&self) -> bool {
        self.debug_mode
    }

    pub fn push_const<T: Into<NkSum>>(&mut self, v: T) -> usize {
        let top = self.consts.len();
        self.consts.push(v.into());
        top
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
        self.funcs.get(&name.into())
    }

    pub fn load(&mut self, lib: SymID) -> Result<SymID> {
        let sym_name = self.sym_name(lib).to_string();
        let mut path = String::new();
        let it = self.var(Builtin::SysLoadPath.sym())?
                     .make_iter()
                     .map_err(|e| e.bop(Builtin::SysLoad))?;
        for (i, p) in it.enumerate() {
            path.push_str(with_ref!(p, String(s) => {Ok(&(*s)[..])})
                          .map_err(|e| e.argn(i as u32)
                                        .bop(Builtin::SysLoadPath))?);
            path.push('/');
            path.push_str(&sym_name);
            let extd = path.len();
            for ext in &[".sp", ".spk", ".lisp"] {
                path.push_str(ext);
                if let Ok(src) = fs::read_to_string(&path) {
                    self.read_compile(&src, Some(Cow::from(path)))?;
                    return Ok(Builtin::Unknown.sym())
                }
                path.drain(extd..).for_each(drop);
            }
            path.clear();
        }
        err!(ModuleNotFound, lib)
    }

    pub fn consts_top(&self) -> usize {
        self.consts.len()
    }

    pub fn var(&self, sym: SymID) -> Result<PV> {
        let idx = self.get_env_global(sym)
                      .ok_or(error!(UndefinedVariable, var: sym))?;
        Ok(self.mem.get_env(idx))
    }

    pub fn get_env_global(&self, name: SymID) -> Option<usize> {
        self.globals.get(&name).copied()
    }

    /// Reads LISP code into an AST.
    pub fn read(&mut self, lisp: &str) -> Result<()> {
        self.mem.read(lisp)
    }

    pub fn read_compile_from(&mut self, path: impl AsRef<Path>) -> Result<PV> {
        let sexpr = fs::read_to_string(path.as_ref())?;
        let name = path.as_ref().file_stem().map(|p| {
            p.to_string_lossy().into_owned()
        }).map(Cow::from);
        self.read_compile(&sexpr, name)
    }

    pub fn read_compile(&mut self, sexpr: &str, file: SourceFileName) -> Result<PV> {
        let toks = tokenize(sexpr, &self.tok_tree)?;
        let mut mods: Vec<SymID> = vec![];
        let mut close = vec![];
        let mut pmods = vec![];
        let mut dots = vec![];
        let mut dot = false;
        let mut num: u32 = 0;
        let mut srcs = vec![];
        let mut src_idx = vec![0];
        let mut cc = crate::comp::R8Compiler::new(self);
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
                                   .map(|s| self.sym_name(s))
                                   .collect::<Vec<_>>()
                                   .join("");
                    return Err(error!(TrailingModifiers, mods)$(.amend($meta))*);
                }
            };
        }
        let mut tokit = toks.into_iter().peekable();
        let mut modfn_pos = 0;
        while let Some(tok) = tokit.next() {
            let Token { line, col, text } = tok;
            srcs.push(LineCol { line, col });
            match text {
                "(" => {
                    src_idx.push(srcs.len());
                    pmods.push(take(&mut mods));
                    close.push(num + 1);
                    dots.push(dot);
                    dot = false;
                    num = 0;
                }
                ")" if close.is_empty() => bail!(TrailingDelimiter { close: ")" }),
                "." if close.is_empty() => bail!(OutsideContext {
                    ctx: Builtin::List,
                    op: Builtin::ConsDot
                }),
                "." if dot => bail!(SyntaxError {
                    msg: "Illegal use of the dot (.) operator".to_string()
                }),
                "." => dot = true,
                ")" => {
                    assert_no_trailing!(Meta::Source(LineCol { line, col }));
                    let cur_srcs = srcs.drain(src_idx.pop().unwrap()..)
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
                            self.expand_from_stack(num, dot)?
                        } else {
                            wrap!(self.mem.list_dot_srcs(num, cur_srcs, dot));
                            let pv = self.mem.pop().unwrap();
                            self.macroexpand_pv(pv, false)?
                        };
                        // ^ macroexpand can eval/defun, so update offsets
                        cc.set_offsets(self);

                        let excv = Excavator::new(&self.mem);
                        let ast = excv.to_ast(v)?;
                        self.mem.clear_tags();
                        if tokit.peek().is_some() {
                            cc.compile_top(ast)?;
                        } else {
                            modfn_pos = cc.compile_top_tail(ast)?;
                        }
                        cc.take(self)?;
                    } else {
                        wrap!(self.mem.list_dot_srcs(num, cur_srcs, dot));
                    }

                    dot = dots.pop().unwrap();
                    num = close.pop()
                               .ok_or_else(
                                   || error!(TrailingDelimiter, close: ")")
                                       .amend(Meta::Source(LineCol { line, col })))?;
                }
                _ => {
                    let sexpr_mod = sexpr_modifier_bt(text)
                        .map(|b| b.sym())
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
                        PV::Sym(self.put_sym(text))
                    };

                    if !close.is_empty() {
                        wrap!(self.mem.push(pv));
                    } else if tokit.peek().is_none() {
                        wrap!(self.mem.push(pv));
                        let pv = self.mem.pop().unwrap();
                        let excv = Excavator::new(&self.mem);
                        let ast = excv.to_ast(pv)?;
                        modfn_pos = cc.compile_top_tail(ast)?;
                        cc.take(self)?;
                    } else {
                        continue;
                    }

                    num += 1;
                }
            }
        }
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

    pub fn expand_from_stack(&mut self, n: u32, dot: bool) -> Result<PV> {
        let op = self.mem.from_top(n as usize);
        let v = if let Some(m) = op.sym().and_then(|op| self.macros.get(&op.into())).copied() {
            if dot {
                return Err(error!(UnexpectedDottedList,).bop(Builtin::Apply))
            }
            let func = self.funcs.get(&m.into()).ok_or("No such function")?;
            if let Err(e) = func.args.check(m, (n - 1) as u16) {
                self.mem.popn(n as usize);
                return Err(e);
            }
            let frame = self.frame;
            self.frame = self.mem.stack.len() - (n as usize) + 1;
            self.mem.push(PV::UInt(0));
            self.mem.push(PV::UInt(frame));
            let pos = func.pos;
            unsafe { self.run_from_unwind(pos)?; }
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
            self.mem.list_dot(n, dot);
            self.mem.pop().unwrap()
        };
        self.macroexpand_pv(v, false)
    }

    fn varor<T>(&mut self, name: SymID, or_default: T) -> Result<T>
        where PV: FromLisp<T>
    {
        if let Ok(var) = self.var(name) {
            var.from_lisp(&mut self.mem)
               .map_err(|e| e.amend(Meta::VarName(OpName::OpSym(name))))
        } else {
            Ok(or_default)
        }
    }

    fn macroexpand_pv(&mut self, mut v: PV, quasi: bool) -> Result<PV> {
        let ind_lim = self.varor(Builtin::LimitsMacroexpandRecursion.sym(),
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
            while let Some(m) = v.op().and_then(|op| self.macros.get(&op.into())).copied() {
                let func = self.funcs.get(&m.into()).ok_or("No such function")?;
                let mut nargs = 0;
                let frame = self.frame;
                self.frame = self.mem.stack.len();
                for arg in v.args() {
                    self.mem.push(arg);
                    nargs += 1;
                }
                if let Err(e) = func.args.check(m, nargs) {
                    self.mem.popn(nargs as usize);
                    self.frame = frame;
                    return Err(e);
                }

                self.mem.push(PV::UInt(0));
                self.mem.push(PV::UInt(frame));

                let pos = func.pos;
                unsafe { self.run_from_unwind(pos)?; }
                invalid!(v); // run_from_unwind
                v = self.mem.pop().expect("Function did not return a value");
                inds += 1;
                if inds > ind_lim {
                    return err!(MacroexpandRecursionLimit, lim: ind_lim);
                }
            }
        }

        let bop = v.bt_op();
        if bop == Some(Builtin::Quote) {
            Ok(v)
        } else if bop == Some(Builtin::Quasi) {
            self.mem.stack.push(v);
            let ni = self.macroexpand_pv(v.inner()?, true)?;
            invalid!(v); // macroexpand_pv
            v = self.mem.stack.pop().unwrap();
            v.set_inner(ni)?;
            Ok(v)
        } else if v.is_atom() {
            Ok(v)
        } else {
            self.mem.push(v);
            let mut dot = false;
            let mut idx = 0;
            loop {
                // self.dump_stack().unwrap();
                let PV::Ref(p) = v else { unreachable!("{v:?}") };
                let Cons { car, cdr } = unsafe { *fastcast(p) };
                let r = if dot {cdr} else {car};
                let ncar = match (bop, idx) {
                    (Some(Builtin::Lambda), 1) |
                    (Some(Builtin::Define), 1) => Ok(r),
                    _ => {
                        self.mem.push(v);
                        let ncar = self.macroexpand_pv(r, quasi);
                        v = self.mem.pop().unwrap();
                        ncar
                    }
                };
                invalid!(car, cdr, r); // ^ macroexpand_pv
                let PV::Ref(p) = v else { unreachable!() };
                let cns = unsafe { fastcast_mut::<Cons>(p) };
                unsafe {
                    let dst = if dot { addr_of_mut!((*cns).cdr) }
                              else   { addr_of_mut!((*cns).car) };
                    *dst = match ncar {
                        Ok(x) => x,
                        Err(e) => {
                            self.mem.pop().unwrap();
                            return Err(e);
                        }
                    };

                    idx += 1;
                    v = match (*cns).cdr.bt_type_of() {
                        Builtin::Nil => break,
                        Builtin::Cons => (*cns).cdr,
                        _ if dot => break,
                        _ => { dot = true; v }
                    }
                }
            }
            let pv = self.mem.pop();
            pv
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
        self.macros.insert(macro_sym.into(), fn_sym);
    }

    pub fn set_macro_character(&mut self, macro_sym: SymID, fn_sym: SymID) {
        let s = self.sym_name(macro_sym).to_string();
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
        match self.funcs.entry(name.into()) {
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

    pub fn sym_name(&self, sym: SymID) -> &str {
        self.mem.symdb
                .name(sym)
                .expect("Assumed present symbol was not present")
    }

    pub fn sym_id(&mut self, name: &str) -> SymID {
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
        let mut pos_to_fn: Vec<(usize, SymIDInt)> = Vec::new();
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
                name = Builtin::Unknown.sym().into();
                (0, 0)
            } else {
                let spec = func.args;
                (spec.env as usize,
                 spec.sum_nargs() as usize)
            };

            let frame = self.frame;
            let args = self.mem.stack.drain(frame..frame+nargs).collect();
            let src = self.get_source(ip);
            frames.push(TraceFrame { args,
                                     func: name.into(),
                                     src });

            self.mem.stack.drain(frame..frame+nenv).for_each(drop);
            if frame >= self.mem.stack.len() {
                vmprintln!(self, "Warning: Incomplete stack trace!");
                break;
            }
            ip = match self.mem.stack[frame] {
                PV::UInt(x) => x,
                _ => {
                    vmprintln!(self, "Warning: Incomplete stack trace!");
                    break;
                }
            };
            self.frame = match self.mem.stack[frame+1] {
                PV::UInt(x) => x,
                _ => {
                    vmprintln!(self, "Warning: Incomplete stack trace!");
                    break;
                }
            };
            self.mem.stack.drain(frame..).for_each(drop);
        }

        Traceback { frames, err }
    }

    // FIXME: This function is super slow, unoptimized, and only for debugging
    fn traceframe(&self, ip: usize) -> SymID {
        let mut pos_to_fn: Vec<(usize, SymIDInt)> = Vec::new();
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

        get_name(ip).into()
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
            println!("{} ({v})", self.sym_name(*k));
        }
    }

    unsafe fn run_from_unwind(&mut self, offs: usize) -> std::result::Result<usize, Traceback> {
        self.catch();
        let res = match self.run_from(offs) {
            Ok(ip) => Ok(ip),
            Err((ip, e)) => Err(self.unwind_traceback(ip, e)),
        };
        self.catch_pop();
        res
    }

    #[inline]
    fn op_clzcall(&mut self,
                  ip: *mut r8c::Op,
                  nargs: u16) -> Result<*mut r8c::Op> {
        let idx = self.mem.stack.len() - nargs as usize - 1;
        let lambda_pv = self.mem.stack[idx];
        with_ref_mut!(lambda_pv, Lambda(lambda) => {
            let sym = Builtin::GreekLambda.sym();
            (*lambda).args.check(sym, nargs)?;
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
        }, Subroutine(subr) => {
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
            let args: Vec<_> = (&self.mem.stack[top - nargs as usize..]).into_iter().copied().collect();

            let dip = self.ip_delta(ip);
            // if self.debug_mode { println!("<subr>::{}:", (*subr).name()) }
            let res = (*subr).call(self, &args[..]);
            invalid!(args); // (*subr).call
            self.mem.stack.drain(idx..).for_each(drop); // drain gang
            self.mem.push(res?);
            // if self.debug_mode {
            //     println!("ret <subr>::{}", (*subr).name());
            //     self.dump_stack()?;
            // }
            Ok(self.ret_to(dip))
        }, Continuation(cont) => {
            ArgSpec::normal(1).check(Builtin::Continuation.sym(), nargs)?;
            let cont_stack = (*cont).take_stack()?;

            let pv = self.mem.pop().unwrap();
            self.mem.stack.drain(idx..).for_each(drop); // drain gang

            // push state
            let dip = self.ip_delta(ip);
            let frame = self.frame;
            let stack = mem::replace(&mut self.mem.stack, cont_stack);
            self.mem.conts.push(stack);

            // call continuation
            self.mem.stack.push(pv);
            self.frame = (*cont).frame;
            let res = unsafe { self.run_from_unwind((*cont).dip) };

            // pop state
            let mut stack = mem::replace(&mut self.mem.stack,
                                         self.mem.conts.pop().unwrap());
            self.frame = frame;

            // handle error
            let res = if let Err(e) = res {
                Err(e.into())
            } else if let Some(pv) = stack.pop() {
                self.mem.push(pv);
                Ok(self.ret_to(dip))
            } else {
                Err(error!(NotEnough,
                           got: 0,
                           expect: 1)
                    .amend(Meta::Op(OpName::OpStr("continuation"))))
            };

            (*cont).put_stack(stack);

            res
        })
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
        // let mut orig = None;
        // if self.debug_mode {
        //     let sym = self.traceframe(offs as usize);
        //     orig = Some(sym);
        //     println!("{}:", self.name(SymID::from(sym)));
        // }
        let mut run = || loop {
            // let op = *ip;
            let ipd = self.ip_delta(ip);
            let op = *self.pmem.get_unchecked(ipd);

            // if self.debug_mode {
            //     match op {
            //         VCALL(f, _) => println!("{}:", self.name(SymID::from(f))),
            //         CALL(ip, _) => {
            //             let sym = self.traceframe(ip as usize);
            //             println!("{}:", self.name(SymID::from(sym)));
            //         }
            //         _ => ()
            //     }
            //     println!("  {}", op);
            // }

            // let op = *ip;
            ip = ip.offset(1);
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
                LIST(n) => {
                    self.mem.list(n)
                },
                VLIST() => {
                    let len = self.mem.pop()?.force_int() as u32;
                    self.mem.list(len);
                }
                CONS() => self.mem.cons(),
                APPEND(n) => self.mem.append(n)?,

                // Iterators
                NXIT(var) => {
                    let offset = (self.frame as isize) + (var as isize);
                    let it = *self.mem.stack.as_ptr().offset(offset);
                    with_ref_mut!(it, Iter(it) => {
                        let elem = (*it).next()
                                        .unwrap_or_else(
                                            || PV::Sym(Builtin::IterStop.sym()));
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
                    let ptr = self.mem.put(vec);
                    self.mem.push(NkAtom::make_ref(ptr));
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
                    let op = Builtin::Get;
                    let idx = match self.mem.pop()? {
                        PV::Int(x) => x as usize,
                        x => return Err(error!(TypeError,
                                               expect: Builtin::Integer,
                                               got: x.bt_type_of()).bop(op).argn(2))
                    };
                    let vec = self.mem.pop()?;
                    let elem = with_ref!(vec, Vector(v) => {
                        (*v).get(idx).ok_or(error!(IndexError, idx))
                    }).map_err(|e| e.bop(op))?;
                    self.mem.push(*elem);
                }
                VSET() => {
                    // (set (get <vec> <idx>) <val>)
                    let op = Builtin::Set;
                    let len = self.mem.stack.len();
                    let args = &mut self.mem.stack[len - 3..];
                    let idx = match args[2] {
                        PV::Int(x) => x as usize,
                        x => return Err(error!(TypeError,
                                               expect: Builtin::Integer,
                                               got: x.bt_type_of()).bop(op).argn(2))
                    };
                    with_ref_mut!(args[1], Vector(v) => {
                        if idx >= (*v).len() {
                            err!(IndexError, idx)
                        } else {
                            *(*v).get_unchecked_mut(idx) = args[0];
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
                                        Cons(_) => { Ok(li.iter().count()) })
                        .map_err(|e| e.bop(Builtin::Len))?;
                    self.mem.push(PV::Int(len as Int));
                }

                // Value creation
                NIL() => self.mem.push(PV::Nil),
                CONSTREF(n) => self.consts[n as usize].push_to(&mut self.mem),
                INST(idx) => {
                    let pv = self.mem.get_env(idx as usize).deep_clone(&mut self.mem);
                    self.mem.push(pv);
                },
                BOOL(i) => self.mem.push(PV::Bool(i != 0)),
                CLZAV(nargs, nenv) => {
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
                ARGSPEC(_nargs, _nopt, _env, _rest) => {}
                CLZR(pos, nenv) => {
                    let ipd = self.ip_delta(ip);
                    let ARGSPEC(nargs, nopt, env, rest) = *self.pmem.get_unchecked(ipd-2) else {
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

                INC(v, d) => match self.mem.stack[self.frame + (v as usize)] {
                    PV::Int(ref mut x) => *x += d as Int,
                    PV::Real(ref mut x) => *x += f32::from(d),
                    x => return Err(RuntimeError::new(format!("Cannot increment: {}", x)).into()),
                },
                DEC(v, d) => match self.mem.stack[self.frame + (v as usize)] {
                    PV::Int(ref mut x) => *x -= d as Int,
                    PV::Real(ref mut x) => *x -= f32::from(d),
                    x => return Err(RuntimeError::new(format!("Cannot decrement: {}", x)).into()),
                },

                // Logic
                EQL() => op2!(r, eq, r.into()),
                EQLP() => {
                    let y = self.mem.stack.pop().unwrap_unchecked();
                    let x = self.mem.stack.pop().unwrap_unchecked();
                    self.mem.stack.push(x.equalp(y).into());
                },
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
                    let n = self.mem.pop()?.force_int() as isize;
                    let d = cmp::min((mul as isize) * n, max as isize);
                    ip = ip.offset(d);
                }
                VCALL(sym, nargs) => {
                    match self.funcs.get(&sym) {
                        Some(func) => {
                            func.args.check(sym.into(), nargs)?;
                            let pos = func.pos;
                            // FIXME: This does not pass in miri because of aliasing
                            // (*ip.sub(1)) = CALL(pos as u32, nargs);
                            self.call_pre(ip);
                            self.frame = self.mem.stack.len() - 2 - (nargs as usize);
                            ip = self.ret_to(pos);
                        },
                        None => if let Some(idx) = self.get_env_global(sym.into()) {
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
                }
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
                CLZCALL(nargs) => ip = self.op_clzcall(ip, nargs)?,
                APL() => {
                    let args = self.mem.pop().unwrap();
                    let nargs = with_ref!(args, Cons(_) => {
                        Ok(args.into_iter().map(|a| self.mem.push(a)).count())
                    }, Vector(xs) => {
                        Ok((*xs).iter().map(|a| self.mem.push(*a)).count())
                    }).map_err(|e| e.bop(Builtin::Apply))?;
                    let nargs: u16 = match nargs.try_into() {
                        Ok(n) => n,
                        Err(e) => {
                            self.mem.popn(nargs);
                            self.mem.push(PV::Nil);
                            return Err(e.into());
                        }
                    };
                    ip = self.op_clzcall(ip, nargs)?;
                }
                CALLCC(dip) => {
                    let dip = self.ip_delta(ip) as isize + dip as isize;
                    let mut stack_dup = self.mem.stack.clone();
                    stack_dup.pop();
                    let cnt = self.mem.put_pv(
                        Continuation::new(stack_dup, self.frame, dip as usize));
                    self.mem.push(cnt);
                    ip = self.op_clzcall(ip, 1)?;
                }
                UNWIND() => {
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
                PUSH(n) => self.mem.push(PV::Int(n as Int)),
                PUSHF(n) => self.mem.push(PV::Real(f32::from_bits(n))),
                CHAR(c) => self.mem.push(PV::Char(char::from_u32_unchecked(c))),
                SYM(id) => self.mem.push(PV::Sym(id.into())),
                SAV(num) => regs.save(&mut self.mem, num)?,
                RST() => regs.restore(&mut self.mem),
                TOP(d) => {
                    let top = self.mem.stack.len() - self.frame;
                    self.mem.push(PV::Int((top as Int) - (d as Int)));
                }
                DUP() => self.mem.dup()?,
                CLZEXP() => self.mem.clz_expand(self.frame)?,

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
                    // if self.debug_mode {
                    //     println!("hcf from {:?}", orig.map(|s| self.name(s)));
                    // }
                    return Ok(())
                },
            }
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
            writeln!(stdout, "{}: {}", idx - frame, val.lisp_to_string(&self.mem))?;
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

    pub fn call_spv(&mut self, sym: SymID, args: impl AsArgs) -> Result<SPV> {
        let res = self.call(sym, args)?;
        Ok(self.mem.make_extref(res))
    }

    pub fn apply_spv(&mut self, f: SPV, args: impl AsArgs) -> Result<PV> {
        let frame = self.frame;
        self.frame = self.mem.stack.len();
        self.mem.push(PV::UInt(0));
        self.mem.push(PV::UInt(frame));
        self.mem.push(f.pv(self));
        let pos = clzcall_pad_dip(args.inner_nargs() as u16);
        args.inner_pusharg(&mut self.mem)?;
        unsafe {
            self.run_from_unwind(pos)?;
        }
        self.mem.pop()
    }

    pub fn eval_pv(&mut self, ast: PV) -> Result<PV> {
        self.macroexpand_pv(ast, false).and_then(|ast| {
            let excv = Excavator::new(&self.mem);
            let ast = excv.to_ast(ast)?;
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
        out.write(b"\n")?;
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

    pub fn set_stdout(&mut self, out: Box<dyn OutStream>) {
        *self.stdout.lock().unwrap() = out;
    }

    pub fn set_stdin(&mut self, inp: Box<dyn InStream>) {
        *self.stdin.lock().unwrap() = inp;
    }

    pub fn dump_all_fns(&self) -> Result<()> {
        let mut funks = self.funcs.iter().map(|(k, v)| ((*k).into(), v.pos)).collect::<Vec<_>>();
        funks.sort_by_key(|(_, v)| *v);
        for funk in funks.into_iter().map(|(u, _)| u) {
            self.dump_fn_code(funk)?
        }
        Ok(())
    }

    pub fn dump_code(&self) -> Result<()> {
        for (i, op) in self.pmem.iter().enumerate() {
            println!("{i:0>8}    {op}")
        }
        Ok(())
    }

    pub fn dump_fn_code(&self, mut name: SymID) -> Result<()> {
        if let Some(mac_fn) = self.macros.get(&name.into()) {
            name = *mac_fn;
        }
        let func = self.funcs.get(&name.into()).ok_or("No such function")?;
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
                return Some((op.name().to_lowercase(),
                             vec![self.labels.get(&((pos + delta) as u32))
                                  .map(|lbl| format!("{}", lbl))
                                  .unwrap_or(format!("{}", delta))
                                  .style_asm_label_ref()
                                  .to_string()]))
            }
            let sym_name = |sym: SymIDInt| self.sym_name(sym.into()).to_string();
            Some((op.name().to_lowercase(), match op {
                VCALL(name, args) => vec![sym_name(name), args.to_string()],
                SYM(sym) => vec![sym_name(sym)],
                _ => return None
            }))
        };

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}({}):",
                 self.sym_name(name).style_asm_fn(),
                 func.args)?;
        for i in start..start+(func.sz as isize) {
            let op = self.pmem[i as usize];
            if let Some(s) = self.labels.get(&(i as u32)) {
                writeln!(stdout, "{}:", s.style_asm_label())?;
            }
            let (name, args) = fmt_special(i, op).unwrap_or(
                (op.name().to_lowercase(),
                 op.args().iter().map(|v| v.to_string()).collect())
            );
            writeln!(stdout, "    {} {}",
                     name.style_asm_op(),
                     args.join(", "))?;
        }

        Ok(())
    }

    #[cfg(feature = "extra")]
    pub fn dump_macro_tbl(&self) -> Result<()> {
        let mut table = Table::new();

        table.load_preset(TABLE_STYLE);
        table.set_header(vec!["Macro", "Function"]);
        for (&macro_sym, &fn_sym) in self.macros.iter() {
            table.add_row(vec![self.sym_name(macro_sym.into()),
                               self.sym_name(fn_sym)]);
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
            table.add_row(vec![name, &id.to_string()]);
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
            table.add_row(vec![self.sym_name(sym),
                               &self.mem
                                    .get_env(idx)
                                    .lisp_to_string(&self.mem),
                               &idx.to_string()]);
        }

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}", table)?;

        Ok(())
    }

    pub fn get_funcs_with_prefix(&self, prefix: &str) -> Vec<SymID> {
        let mut funcs = Vec::new();
        for (&sym, _) in self.funcs.iter() {
            if self.sym_name(sym.into()).starts_with(prefix) {
                funcs.push(sym.into())
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
            table.add_row(vec![self.sym_name(sym.into()),
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
                                                     name.into(),
                                                     f.pos.try_into().unwrap())));
        LispModule::new(&self.pmem, &self.mem.symdb, &self.consts, vec![], exports)
    }
}
