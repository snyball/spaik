//! SPAIK R8 Virtual Machine

#[cfg(feature = "repl")]
use comfy_table::Table;

use crate::{
    ast::{Value, ValueKind, Excavator},
    chasm::{ASMOp, ChASMOpName, Lbl, ASMPV},
    compile::{pv_to_value, Builtin, Linked, R8Compiler, SourceList},
    error::{Error, ErrorKind, Source, OpName, Meta, LineCol, SourceFileName},
    fmt::LispFmt,
    module::{LispModule, Export, ExportKind},
    nuke::*,
    nkgc::{Arena, Cons, SymID, SymIDInt, VLambda, PV, SPV, self},
    sexpr_parse::{Parser, sexpr_modified_sym_to_str, sexpr_modifier_bt, string_parse, tokenize, Fragment, standard_lisp_tok_tree},
    subrs::{IntoLisp, Subr, IntoSubr, FromLisp},
    sym_db::SymDB, FmtErr, tok::Token, limits,
};
use fnv::FnvHashMap;
use std::{io, fs, borrow::Cow, cmp, collections::HashMap, convert::TryInto, fmt::{self, Debug, Display}, io::prelude::*, mem::{self, replace}, ptr, slice, sync::Mutex};

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
    // CALL(dip: i32, nargs: u16),
    VCALL(func: SymIDInt, nargs: u16),
    // TODO: APPLY()
    CLZCALL(nargs: u16),
    RET(),
    CALLCC(dip: i32),
    UNWIND(),
    HCF(),

    // Stack operations
    CONSTREF(idx: u32),
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
    SYM(id: SymIDInt),
    CHAR(c: u32),
    CLZ(sym: SymIDInt, nenv: u16),
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
    ($vm:expr, $($fmt:expr),+) => {
        $vm.print_fmt(format_args!($($fmt),+)).unwrap();
        $vm.println(&"").unwrap();
    };
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

#[cfg(feature = "repl")]
const TABLE_STYLE: &str = comfy_table::presets::UTF8_BORDERS_ONLY;

#[derive(Debug, Clone, Eq, PartialEq)]
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

    pub fn err<T>(msg: String) -> Result<T, RuntimeError> {
        Err(RuntimeError::new(msg))
    }
}

macro_rules! comma_list_len {
    ( $head:pat ) => { 1 };
    ( $head:pat, $( $tail:pat ),+ ) => { 1 + comma_list_len!($($tail),+) }
}

type StackOpFn<T> = fn(&mut Vec<T>) -> Result<(), Error>;

macro_rules! stack_op {
    ( $name:literal [ $( $arg:pat ),+ ] => $action:block ) => {
        |st: &mut Vec<PV>| -> Result<(), Error> {
            const NARGS: usize = comma_list_len!($($arg),+);
            const EXPR_FMT: &'static str = stringify!($($arg),+);
            if st.len() < NARGS {
                return Err(RuntimeError::new(format!(
                    "Not enough arguments for: {}", EXPR_FMT)).into());
            }
            let slice = &st[st.len() - NARGS..];
            #[allow(unused_imports)]
            use PV::*;
            let res: Result<_, Error> = match slice {
                [$($arg),+] => { $action }
                _ => {
                    let types = slice.iter()
                                     .map(|v| v.bt_type_of())
                                     .map(|v| v.get_str())
                                     .collect::<Vec<_>>()
                                     .join(" ");
                    return Err(RuntimeError::new(
                        format!("Illegal arguments: ({} {})", $name, types)).into())
                },
            };
            st.truncate(st.len() - NARGS);
            st.push(PV::from(res?));
            Ok(())
        }
    }
}

fn tostring(vm: &R8VM, x: PV) -> String {
    match x {
        PV::Ref(y) => match unsafe { (*y).match_ref() } {
            NkRef::String(s) => s.clone(),
            _ => x.lisp_to_string(&vm.mem),
        },
        PV::Char(c) => format!("{c}"),
        _ => x.lisp_to_string(&vm.mem),
    }
}

macro_rules! featurefn {
    ($ft:expr, $e:expr) => {{
        #[cfg(feature = $ft)]
        let funk = || -> Result<(), Error> {
            $e;
            Ok(())
        };
        #[cfg(not(feature = $ft))]
        let funk = || -> Result<(), Error> {
            err!(MissingFeature, flag: $ft)
        };
        funk()
    }};
}

macro_rules! subr {
    (fn $name:ident[$name_s:expr](&mut $self:ident, $vm:ident : &mut R8VM, $args:ident : &[PV])
                    -> Result<PV, Error> $body:block) => {
        #[derive(Clone, Copy, Debug)]
        pub struct $name;

        unsafe impl Subr for $name {
            fn call(&mut $self, $vm: &mut R8VM, $args: &[PV]) -> Result<PV, Error> $body
            fn name(&self) -> &'static str { $name_s }
        }
    };

    (fn $name:ident(&mut $self:ident, $vm:ident : &mut R8VM, $args:ident : &[PV])
                    -> Result<PV, Error> $body:block) => {
        subr!(fn $name[stringify!($name)](&mut $self, $vm : &mut R8VM, $args : &[PV])
                                          -> Result<PV, Error> $body);
    };

    (fn $name:ident(&mut $self:ident, $vm:ident : &mut R8VM, args: ($($arg:ident),*)) -> Result<PV, Error> $body:block) => {
        subr!(fn $name(&mut $self, $vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
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
    ($(fn $name:ident($($inner:tt)*) -> Result<PV, Error> $body:block)*) => {
        $(subr!(fn $name($($inner)*) -> Result<PV, Error> $body);)*
    };
}

#[allow(non_camel_case_types)]
mod sysfns {
    use std::{fmt::Write, convert::Infallible, borrow::Cow};

    use crate::{subrs::{Subr, IntoLisp}, nkgc::PV, error::{Error, ErrorKind}, fmt::{LispFmt, FmtWrap}, compile::Builtin};
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
                write!(&mut out, "{s}").unwrap();
                Ok(())
            }).or_else(|_| -> Result<(), Infallible> {
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
        fn println(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            let s = tostring(vm, *x);
            vm.println(&s)?;
            Ok(*x)
        }

        fn print(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            let s = tostring(vm, *x);
            vm.print(&s)?;
            Ok(*x)
        }

        fn string(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            x.lisp_to_string(&vm.mem)
             .into_pv(&mut vm.mem)
        }

        fn eval(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            vm.mem.push(*x);
            vm.mem.list(1);
            let x = vm.mem.pop().unwrap();
            vm.eval_ast(x)
        }

        fn read(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            vm.read(&tostring(vm, *x))?;
            vm.mem.pop()
        }

        fn concat(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            join_str(vm, args.iter().copied(), "").into_pv(&mut vm.mem)
        }

        fn error(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            if let PV::Sym(name) = *x {
                err!(LibError, name)
            } else {
                Err(error!(TypeError,
                           expect: Builtin::Symbol.sym(),
                           got: x.type_of())
                    .op(Builtin::Error.sym())
                    .argn(1))
            }
        }

        fn join(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            let emap = |e: Error| e.op(Builtin::Join.sym()).argn(1);
            let (it, sep) = match args {
                [xs, PV::Char(s)] => (xs.make_iter().map_err(emap)?,
                                      Cow::from(s.to_string())),
                [xs, PV::Sym(s)] => (xs.make_iter().map_err(emap)?,
                                     Cow::from(vm.sym_name(*s))),
                [xs, o] => (xs.make_iter().map_err(emap)?, with_ref!(*o, String(s) => {
                    Ok(Cow::from(s))
                }).map_err(|e| e.op(Builtin::Join.sym()).argn(2))?),
                [xs] => (xs.make_iter()?, Cow::from("")),
                _ => return Err(error!(ArgError,
                                       expect: ArgSpec::opt(1, 1),
                                       got_num: args.len() as u32)
                                .op(Builtin::Join.sym()))
            };
            join_str(vm, it, sep).into_pv(&mut vm.mem)
        }

        fn iter(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            x.make_iter().map_err(|e| e.argn(1))?.into_pv(&mut vm.mem)
        }

        fn exit(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            let status = args.first().copied()
                                     .unwrap_or_else(
                                         || PV::Sym(Builtin::KwOk.sym()));
            Err(Error { ty: ErrorKind::Exit {
                status: status.try_into().map_err(|e: Error|
                                                  e.argn(1).op(Builtin::Exit.sym()))?
            }, meta: Default::default() })
        }

        fn instant(&mut self, vm: &mut R8VM, args: ()) -> Result<PV, Error> {
            #[cfg(not(target_arch = "wasm32"))]
            return Ok(PV::Real(vm.mem.stats().time.as_secs_f32()));
            #[cfg(target_arch = "wasm32")]
            return Ok(PV::Nil);
        }

        fn dump_macro_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV, Error> {
            featurefn!("repl", vm.dump_macro_tbl()?)?;
            Ok(PV::Nil)
        }

        fn dump_sym_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV, Error> {
            featurefn!("repl", vm.dump_symbol_tbl()?)?;
            Ok(PV::Nil)
        }

        fn dump_env_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV, Error> {
            featurefn!("repl", vm.dump_env_tbl()?)?;
            Ok(PV::Nil)
        }

        fn dump_fn_tbl(&mut self, vm: &mut R8VM, args: ()) -> Result<PV, Error> {
            featurefn!("repl", vm.dump_fn_tbl()?)?;
            Ok(PV::Nil)
        }

        fn disassemble(&mut self, vm: &mut R8VM, args: (func)) -> Result<PV, Error> {
            featurefn!("repl", vm.dump_fn_code((*func).try_into()?)?)?;
            Ok(PV::Nil)
        }

        fn disassemble_all(&mut self, vm: &mut R8VM, args: ()) -> Result<PV, Error> {
            featurefn!("repl", vm.dump_all_code()?)?;
            Ok(PV::Nil)
        }

        fn macroexpand(&mut self, vm: &mut R8VM, args: (ast)) -> Result<PV, Error> {
            vm.macroexpand_pv(*ast, false)
        }

        fn read_compile(&mut self, vm: &mut R8VM, args: (code)) -> Result<PV, Error> {
            with_ref_mut!(*code, String(s) => { vm.read_compile(s, None) })
        }

        fn load(&mut self, vm: &mut R8VM, args: (lib)) -> Result<PV, Error> {
            Ok(PV::Sym(vm.load((*lib).try_into()?)?))
        }

        fn pow(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV, Error> {
            x.pow(y)
        }

        fn modulo(&mut self, vm: &mut R8VM, args: (x, y)) -> Result<PV, Error> {
            x.modulo(y)
        }

        fn set_macro(&mut self, vm: &mut R8VM, args: (macro_name, fn_name)) -> Result<PV, Error> {
            vm.set_macro((*macro_name).try_into()?,
                         (*fn_name).try_into()?);
            Ok(PV::Nil)
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct make_symbol;

    unsafe impl Subr for make_symbol {
        fn call(&mut self, vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            match args {
                [s @ PV::Sym(_)] => Ok(*s),
                [r] => with_ref!(*r, String(s) => {
                    Ok(PV::Sym(vm.mem.symdb.put_ref(s)))
                }),
                _ => Err(error!(ArgError,
                                expect: ArgSpec::normal(1),
                                got_num: args.len() as u32)
                         .op(Builtin::MakeSymbol.sym()))
            }
        }
        fn name(&self) -> &'static str { "make-symbol" }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct sum;

    unsafe impl Subr for sum {
        fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
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
        fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            match args {
                [PV::Sym(id)] => Ok(PV::Int((*id).try_into()?)),
                [x] => Err(error!(TypeError,
                                  expect: Builtin::Symbol.sym(),
                                  got: x.type_of(),)
                           .op(Builtin::SymID.sym(),)
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
        fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            subr_args!((x) self _vm args { Ok(PV::Sym(x.type_of())) })
        }
        fn name(&self) -> &'static str { "type-of" }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct asum;

    unsafe impl Subr for asum {
        fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            if args.len() == 1 {
                return PV::Int(0).sub(&args[0])
            }
            let mut it = args.iter();
            let mut s = it.next().ok_or(error!(ArgError,
                                               expect: ArgSpec::rest(1, 0),
                                               got_num: 0)
                                        .op(Builtin::Sub.sym()))
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
        fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
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
        fn call(&mut self, _vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            if args.len() == 1 {
                return PV::Int(1).div(&args[0])
            }
            let mut it = args.iter();
            let mut s = it.next().ok_or(error!(ArgError,
                                               expect: ArgSpec::rest(1, 0),
                                               got_num: 0)
                                        .op(Builtin::Div.sym()))
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
        fn call(&mut self, vm: &mut R8VM, _args: &[PV]) -> Result<PV, Error> {
            vm.print_fmt(format_args!("{:?}", vm.mem.stats()))?;
            vm.println(&"")?;
            Ok(PV::Nil)
        }
        fn name(&self) -> &'static str { "dump-gc-stats" }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct dump_stack;

    unsafe impl Subr for dump_stack {
        fn call(&mut self, vm: &mut R8VM, _args: &[PV]) -> Result<PV, Error> {
            vm.dump_stack()?;
            Ok(PV::Nil)
        }
        fn name(&self) -> &'static str { "dump-stack" }
    }

    // struct Fns;
    // #[spaikfn(Fns)]
    // fn push(v: &mut Vec<PV>) {
    // }
}

pub type ArgInt = u16;

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq)]
pub struct ArgSpec {
    pub nargs: ArgInt,
    pub nopt: ArgInt,
    pub rest: bool,
    pub env: ArgInt,
}

impl fmt::Display for ArgSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

    pub fn check(&self, fn_sym: SymID, nargs: u16) -> Result<(), Error> {
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
    pos: usize,
    sz: usize,
    args: ArgSpec,
}

impl Func {
    pub fn adjust(&mut self, pos: usize) {
        self.pos -= pos;
    }
}

// TODO:
#[allow(dead_code)]
struct Module {
    pmem: Vec<r8c::Op>,
    consts: Vec<NkSum>,
    globals: FnvHashMap<SymID, usize>,
    macros: FnvHashMap<SymIDInt, SymID>,
    funcs: FnvHashMap<SymIDInt, Func>,
    func_labels: FnvHashMap<SymID, HashMap<usize, Lbl>>,
    symbols: Vec<(SymID, String)>,
    env: Vec<Value>,
}

pub trait OutStream: io::Write + Debug + Send {}
impl<T> OutStream for T where T: io::Write + Debug + Send {}

pub trait InStream: io::Read + Debug + Send {}
impl<T> InStream for T where T: io::Read + Debug + Send {}

#[derive(Debug)]
pub struct R8VM {
    /// Memory
    pmem: Vec<r8c::Op>,
    consts: Vec<NkSum>,
    pub(crate) mem: Arena,
    globals: FnvHashMap<SymID, usize>,

    // Named locations/objects
    breaks: FnvHashMap<usize, r8c::Op>,
    macros: FnvHashMap<SymIDInt, SymID>,
    funcs: FnvHashMap<SymIDInt, Func>,
    func_labels: FnvHashMap<SymID, FnvHashMap<u32, Lbl>>,
    func_arg_syms: FnvHashMap<SymID, Vec<SymID>>,
    srctbl: SourceList,
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
            debug_mode: false,
            frame: Default::default(),
            srctbl: Default::default(),
        }
    }
}

macro_rules! def_stack_op {
    ($($name:ident($lisp_name:literal) : [ $($match:pat),+ ] => $body:block;)+) => {
        $(const $name: StackOpFn<PV> = stack_op!($lisp_name [$($match),+] => $body);)+
    };
}

def_stack_op! {
    GT_OP(">"):   [x, y] => { x.gt(y) };
    GTE_OP(">="): [x, y] => { x.gte(y) };
    LT_OP("<"):   [x, y] => { x.lt(y) };
    LTE_OP("<="): [x, y] => { x.lte(y) };
    ADD_OP("+"):  [x, y] => { x.add(y) };
    SUB_OP("-"):  [x, y] => { x.sub(y) };
    DIV_OP("/"):  [x, y] => { x.div(y) };
    MUL_OP("*"):  [x, y] => { x.mul(y) };
    EQL_OP("="):  [x, y] => { Ok(Bool(x == y)) };
    EQLP_OP("eq?"):  [x, y] => { Ok(Bool(x.equalp(*y))) };
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
    fn save(&mut self, mem: &mut Arena, num: u8) -> Result<(), RuntimeError> {
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

// FIXME: The error handling in this macro fucks up the stack.
#[allow(unused_macros)]
macro_rules! vm_call_with {
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
    fn pushargs(self, args: &[SymID], mem: &mut Arena) -> Result<(), Error>;
}

pub trait Args {
    fn pusharg(self, mem: &mut Arena) -> Result<(), Error>;
    fn pusharg_ref(&self, mem: &mut Arena) -> Result<(), Error>;
    fn nargs(&self) -> usize;
}

pub trait AsArgs {
    fn inner_pusharg(self, mem: &mut Arena) -> Result<(), Error>;
    fn inner_nargs(&self) -> usize;
}

impl<T> AsArgs for T where T: Args {
    #[inline(always)]
    fn inner_pusharg(self, mem: &mut Arena) -> Result<(), Error> {
        self.pusharg(mem)
    }

    #[inline(always)]
    fn inner_nargs(&self) -> usize {
        self.nargs()
    }
}

impl AsArgs for Box<dyn Args + Send> {
    fn inner_pusharg(self, mem: &mut Arena) -> Result<(), Error> {
        self.pusharg_ref(mem)
    }

    fn inner_nargs(&self) -> usize {
        self.nargs()
    }
}

impl Args for &[PV] {
    fn pusharg(self, mem: &mut Arena) -> Result<(), Error> {
        for arg in self.iter().copied() {
            mem.push(arg);
        }
        Ok(())
    }

    fn pusharg_ref(&self, mem: &mut Arena) -> Result<(), Error> {
        for arg in self.into_iter().copied() {
            mem.push(arg);
        }
        Ok(())
    }

    fn nargs(&self) -> usize {
        self.len()
    }
}

impl<const N: usize> Args for &[PV; N] {
    fn pusharg(self, mem: &mut Arena) -> Result<(), Error> {
        for arg in self.iter().copied() {
            mem.push(arg);
        }
        Ok(())
    }

    fn pusharg_ref(&self, mem: &mut Arena) -> Result<(), Error> {
        for arg in self.into_iter().copied() {
            mem.push(arg);
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
            fn pusharg(self, mem: &mut Arena) -> Result<(), Error> {
                #[allow(non_snake_case)]
                let ($($arg),*,) = self;
                $(#[allow(non_snake_case)]
                  let $arg = $arg.into_pv(mem)?;
                  mem.push($arg);)*
                Ok(())
            }

            fn pusharg_ref(&self, mem: &mut Arena) -> Result<(), Error> {
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
    fn pusharg(self, _mem: &mut Arena) -> Result<(), Error> { Ok(()) }
    fn pusharg_ref(&self, _mem: &mut Arena) -> Result<(), Error> { Ok(()) }
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
        addfn!("read-compile", read_compile);
        addfn!("type-of", type_of);
        addfn!("sym-id", sym_id);
        addfn!("set-macro", set_macro);

        // Debug
        addfn!("disassemble-all", disassemble_all);
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

        vm.eval("(define (<ξ>::set-macro! macro fn) (set-macro macro fn) nil)")
          .unwrap();
        vm.eval("(set-macro 'set-macro! '<ξ>::set-macro!)")
          .unwrap();

        vm
    }

    pub fn new() -> R8VM {
        let mut vm = R8VM::no_std();

        let core_sym = vm.sym_id("<ζ>::core");
        let core = include_str!("../lisp/core.lisp");
        let entry = vm.load_with("<ζ>::core", core_sym, core)
                      .fmt_unwrap(&vm);
        vm.call(entry, ()).fmt_unwrap(&vm);

        vm
    }

    pub fn has_mut_extrefs(&self) -> bool {
        self.mem.has_mut_extrefs()
    }

    pub fn call_by_enum(&mut self, enm: impl EnumCall) -> Result<PV, Error> {
        let name = enm.name(&mut self.mem);
        let args = self.func_arg_syms.get(&name).map(|v| &**v).ok_or(
            error!(UndefinedFunction, name)
        )?;
        let nargs = args.len();
        Ok(vm_call_with!(self, name, nargs, { enm.pushargs(args, &mut self.mem)? }))
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

    pub fn set<T: IntoLisp>(&mut self, var: SymID, obj: T) -> Result<(), Error> {
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

    pub fn add_func(&mut self, name: SymID, code: Linked, args: ArgSpec, arg_names: Vec<SymID>) {
        let (asm, labels, consts, srcs) = code;
        self.funcs.insert(name.into(), Func {
            pos: self.pmem.len(),
            sz: asm.len(),
            args
        });
        self.func_labels.insert(name, labels);
        self.func_arg_syms.insert(name, arg_names);
        self.add_code(asm, Some(consts), Some(srcs));
    }

    pub fn load_with<S: AsRef<str>>(&mut self, src_path: S, lib: SymID, code: S) -> Result<SymID, Error> {
        let sym_name = self.sym_name(lib).to_string();
        let ast = Parser::parse(self,
                                code.as_ref(),
                                Some(Cow::from(src_path.as_ref().to_string())))?;
        let mut cc = R8Compiler::new(self);
        cc.compile_top(true, &ast)?;
        let globs = cc.globals()
                      .map(|v| v.map(|(u, v)| (*u, *v))
                                .collect::<Vec<_>>());
        let (mut asm, lbls, consts, srcs) = cc.link()?;
        if let Some(globs) = globs {
            for (name, idx) in globs {
                self.globals.insert(name, idx);
            }
        }
        asm.push(r8c::Op::RET());
        let fn_sym = self.mem.symdb.put(format!("<Σ>::{}", sym_name));
        self.add_func(fn_sym, (asm, lbls, consts, srcs), ArgSpec::none(), vec![]);
        Ok(fn_sym)
    }

    pub fn load(&mut self, lib: SymID) -> Result<SymID, Error> {
        let sym_name = self.sym_name(lib).to_string();
        let mut path = String::new();
        let it = self.var(Builtin::SysLoadPath.sym())?
                     .make_iter()
                     .map_err(|e| e.op(Builtin::SysLoad.sym()))?;
        for (i, p) in it.enumerate() {
            path.push_str(with_ref!(p, String(s) => {Ok(&*s)})
                          .map_err(|e| e.argn(i as u32)
                                        .op(Builtin::SysLoadPath.sym()))?);
            path.push_str("/");
            path.push_str(&sym_name);
            let extd = path.len();
            for ext in &[".sp", ".spk", ".lisp"] {
                path.push_str(&ext);
                if let Ok(src) = fs::read_to_string(&path) {
                    return self.load_with(path, lib, src);
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

    pub fn var(&self, sym: SymID) -> Result<PV, Error> {
        let idx = self.get_env_global(sym)
                      .ok_or(error!(UndefinedVariable, var: sym))?;
        Ok(self.mem.get_env(idx))
    }

    pub fn get_env_global(&self, name: SymID) -> Option<usize> {
        self.globals.get(&name).copied()
    }

    /// Reads LISP code into an AST.
    pub fn read(&mut self, lisp: &str) -> Result<(), Error> {
        self.mem.read(lisp)
    }

    pub fn eval_macroexpand<'z>(&mut self,
                                v: &'z mut Value) -> Result<&'z mut Value, Error> {
        if let Some(ast) = self.expand(v) {
            *v = ast?;
            return self.eval_macroexpand(v);
        }
        if let Some(Builtin::EvalWhen) = v.bt_op() {
            *v = R8Compiler::new(self).bt_eval_when(v)?;
            return Ok(v);
        }
        for arg in v.args_mut() {
            self.eval_macroexpand(arg)?;
        }
        Ok(v)
    }

    pub fn macroexpand<'z>(&mut self,
                           v: &'z mut Value) -> Result<&'z mut Value, Error> {
        if let Some(ast) = self.expand(v) {
            *v = ast?;
            return self.macroexpand(v);
        }
        for arg in v.args_mut() {
            self.macroexpand(arg)?;
        }
        Ok(v)
    }

    pub fn macroexpand_seq<'z>(&mut self,
                               v: &'z mut Value) -> Result<&'z mut Value, Error> {
        for v in v.iter_mut() {
            self.macroexpand(v)?;
        }
        Ok(v)
    }

    pub fn read_compile(&mut self, sexpr: &str, file: SourceFileName) -> Result<PV, Error> {
        lazy_static! {
            static ref TREE: Fragment = standard_lisp_tok_tree();
        }
        let toks = tokenize(sexpr, &TREE)?;
        let mut mods: Vec<Builtin> = vec![];
        let mut close = vec![];
        let mut pmods = vec![];
        let mut dots = vec![];
        let mut dot = false;
        let mut num: u32 = 0;
        let mut srcs = vec![];
        let mut src_idx = vec![0];
        macro_rules! wrap {
            ($push:expr) => {
                $push;
                while let Some(m) = mods.pop() {
                    let p = self.mem.pop().expect("No expr to wrap");
                    self.mem.push(PV::Sym(m.sym()));
                    self.mem.push(p);
                    self.mem.list(2);
                }
            };
        }
        macro_rules! assert_no_trailing {
            ($($meta:expr),*) => {
                if !mods.is_empty() {
                    let mods = mods.into_iter()
                                   .map(sexpr_modified_sym_to_str)
                                   .collect::<Option<Vec<_>>>()
                                   .unwrap()
                                   .join("");
                    return Err(error!(TrailingModifiers, mods)$(.amend($meta))*);
                }
            };
        }
        for tok in toks.into_iter() {
            let Token { line, col, text } = tok;
            srcs.push(LineCol { line, col });
            match text {
                "(" => {
                    src_idx.push(srcs.len());
                    pmods.push(replace(&mut mods, vec![]));
                    close.push(num + 1);
                    dots.push(dot);
                    dot = false;
                    num = 0;
                }
                ")" => {
                    assert_no_trailing!(Meta::Source(LineCol { line, col }));
                    let cur_srcs = srcs.drain(src_idx.pop().unwrap()..)
                                       .map(|lc| lc.into_source(file.clone()));
                    mods = pmods.pop().expect("Unable to wrap expr");
                    if close.len() == 1 {
                        let v = if mods.is_empty() {
                            let idx = self.mem.stack.len() - num as usize;
                            let stack = replace(&mut self.mem.stack, vec![]);
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

                        let excv = Excavator::new(&self.mem);
                        let ast = excv.to_ast(v)?;
                        println!("{}", ast);

                        self.mem.push(v)
                    } else {
                        wrap!(self.mem.list_dot_srcs(num, cur_srcs, dot));
                    }

                    num = close.pop()
                               .ok_or_else(
                                   || error!(TrailingDelimiter, close: ")")
                                       .amend(Meta::Source(LineCol { line, col })))?;
                }
                _ => {
                    let pv = if let Some(m) = sexpr_modifier_bt(text) {
                        mods.push(m);
                        continue;
                    } else if let Ok(int) = text.parse() {
                        PV::Int(int)
                    } else if let Ok(num) = text.parse() {
                        PV::Real(num)
                    } else if let Some(strg) = tok.inner_str() {
                        self.mem.put(string_parse(&strg)?)
                    } else if text == "true" {
                        PV::Bool(true)
                    } else if text == "false" {
                        PV::Bool(false)
                    } else {
                        PV::Sym(self.put_sym(text))
                    };
                    wrap!(self.mem.push(pv));
                    num += 1;
                }
            }
        }
        assert_no_trailing!();
        let srcs = srcs.into_iter()
                       .map(|lc| lc.into_source(file.clone()));
        self.mem.list_dot_srcs(num, srcs, false);
        Ok(self.mem.pop().expect("Unable to pop finalized list"))
    }

    pub fn expand_from_stack(&mut self, n: u32, dot: bool) -> Result<PV, Error> {
        let op = self.mem.from_top(n as usize);
        let v = if let Some(m) = op.op().and_then(|op| self.macros.get(&op.into())).copied() {
            if dot {
                return Err(error!(UnexpectedDottedList,).op(sym!(Apply)))
            }
            let func = self.funcs.get(&m.into()).ok_or("No such function")?;
            if let Err(e) = func.args.check(m.into(), (n - 1) as u16) {
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

    pub fn varor<T>(&mut self, name: SymID, or_default: T) -> Result<T, Error>
        where PV: FromLisp<T>
    {
        if let Ok(var) = self.var(name) {
            var.from_lisp(&mut self.mem)
               .map_err(|e| e.amend(Meta::VarName(OpName::OpSym(name))))
        } else {
            Ok(or_default)
        }
    }

    pub fn macroexpand_pv(&mut self, mut v: PV, quasi: bool) -> Result<PV, Error> {
        let ind_lim = self.varor(Builtin::LimitsMacroexpandRecursion.sym(),
                                 limits::MACROEXPAND_RECURSION)?;

        if quasi && v.bt_op() == Some(Builtin::Unquote) {
            let i = self.macroexpand_pv(v.inner().map_err(|e| e.op(sym!(Unquote)))?,
                                        false)?;
            v.set_inner(i)?;
            return Ok(v)
        } else if !quasi {
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
                if let Err(e) = func.args.check(m.into(), nargs) {
                    self.mem.popn(nargs as usize);
                    self.frame = frame;
                    return Err(e);
                }

                self.mem.push(PV::UInt(0));
                self.mem.push(PV::UInt(frame));

                let pos = func.pos;
                unsafe { self.run_from_unwind(pos)?; }
                v = self.mem.pop().expect("Function did not return a value");
                inds += 1;
                if inds > ind_lim {
                    return err!(MacroexpandRecursionLimit, lim: ind_lim);
                }
            }
        }

        if v.bt_op() == Some(Builtin::Quote) {
            Ok(v)
        } else if v.bt_op() == Some(Builtin::Quasi) {
            let i = v.inner()?;
            v.set_inner(self.macroexpand_pv(i, true)?)?;
            Ok(v)
        } else if v.is_atom() {
            Ok(v)
        } else {
            self.mem.push(v);
            let mut dot = false;
            loop {
                assert_let!(PV::Ref(p) => p = p, v);
                let rf = unsafe{(*p).match_ref()};
                if let NkRef::Cons(Cons { car, cdr }) = rf {
                    self.mem.push(v);
                    let ncar = self.macroexpand_pv(if dot {*cdr} else {*car}, quasi);
                    v = self.mem.pop().unwrap();
                    assert_let!(PV::Ref(p) => p = p, v);
                    let rf = unsafe{(*p).match_mut()};
                    if let NkMut::Cons(Cons { ref mut car, ref mut cdr }) = rf {
                        let dst = if dot { &mut *cdr } else { car };
                        *dst = match ncar {
                            Ok(x) => x,
                            Err(e) => {
                                self.mem.pop().unwrap();
                                return Err(e);
                            }
                        };
                        v = match cdr.bt_type_of() {
                            Builtin::Nil => break,
                            Builtin::Cons => *cdr,
                            _ if dot => break,
                            _ => { dot = true; v }
                        }
                    } else {
                        unreachable!();
                    }
                } else {
                    unreachable!();
                }
            }
            self.mem.pop()
        }
    }

    /**
     * Add code into the VM, taking care to update the const references
     * relative to the ones that already exist in the VM.
     *
     * # Arguments
     *
     * - `code` : Bytecode to be added.
     * - `labels` : Optional debug labels.
     * - `consts` : Constants referenced by the bytecode.
     */
    pub fn add_code(&mut self,
                    mut code: Vec<r8c::Op>,
                    consts: Option<Vec<NkSum>>,
                    srcs: Option<SourceList>)
    {
        let const_rel = self.consts.len() as u32;
        for op in code.iter_mut() {
            if let r8c::Op::CONSTREF(ref mut i) = *op {
                *i += const_rel;
            }
        }
        let offset = self.pmem.len();
        if let Some(srcs) = srcs {
            for (idx, v) in srcs.into_iter() {
                self.srctbl.push((idx + offset, v));
            }
        }
        self.pmem.extend(code);
        if let Some(consts) = consts {
            self.consts.extend(consts);
        }
    }

    pub fn get_source(&self, idx: usize) -> Source {
        let src_idx = match self.srctbl.binary_search_by(|(u, _)| u.cmp(&idx)) {
            Ok(i) => i,
            Err(i) => (i as isize - 1).max(0) as usize
        };
        self.srctbl[src_idx].1.clone()
    }

    /**
     * Add some code and run it, returning the result.
     *
     * SAFETY: Safe as long as `code` is well-formed.
     */
    pub unsafe fn add_and_run(&mut self,
                              code: Vec<r8c::Op>,
                              consts: Option<Vec<NkSum>>,
                              srcs: Option<SourceList>)
                              -> Result<PV, Error>
    {
        let c_start = self.pmem.len();
        let prev_top = self.mem.stack.len();
        self.add_code(code, consts, srcs);
        self.pmem.push(r8c::Op::RET());
        self.set_frame(0);
        self.run_from_unwind(c_start)?;
        if self.mem.stack.len() > prev_top {
            let ret = self.mem.pop()
                              .expect("Logic Error");
            self.mem.stack.truncate(prev_top);
            Ok(ret)
        } else {
            Ok(PV::Nil)
        }
    }

    pub fn eval_ast(&mut self, root: PV) -> Result<PV, Error> {
        let ast = unsafe { pv_to_value(root, &Source::none()) };
        let mut cc = R8Compiler::new(self);
        cc.compile_top(true, &ast)?;
        let (asm, _, consts, srcs) = cc.link()?;
        unsafe {
            self.add_and_run(asm, Some(consts), Some(srcs))
        }
    }

    pub fn eval(&mut self, expr: &str) -> Result<PV, Error> {
        let ast = Parser::parse(self, expr, None)?;
        let mut cc = R8Compiler::new(self);
        // cc.estack.push(Env::empty());
        cc.compile_top(true, &ast)?;
        let globs = cc.globals()
                      .map(|v| v.map(|(u, v)| (*u, *v))
                                .collect::<Vec<_>>());
        let (asm, _, consts, srcs) = cc.link()?;
        if let Some(globs) = globs {
            for (name, idx) in globs {
                self.globals.insert(name, idx);
            }
        }
        unsafe {
            self.add_and_run(asm, Some(consts), Some(srcs))
        }
    }

    pub fn push_ast(&mut self, v: &Value) {
        self.mem.push_ast(v);
    }

    pub unsafe fn pull_ast(&self, v: PV, src: &Source) -> Value {
        let kind = match v {
            PV::Sym(sym) => ValueKind::Symbol(sym),
            PV::Nil => ValueKind::Nil,
            PV::Int(x) => ValueKind::Int(x),
            PV::Bool(x) => ValueKind::Bool(x),
            PV::Real(x) => ValueKind::Real(x),
            PV::Ref(p) => match (*p).match_ref() {
                NkRef::Cons(Cons { car, cdr }) => {
                    let src = self.mem.get_tag(p).unwrap_or(src);
                    ValueKind::Cons(Box::new(self.pull_ast(*car, src)),
                                    Box::new(self.pull_ast(*cdr, src)))
                },
                NkRef::String(s) => ValueKind::String(s.clone()),
                NkRef::PV(v) => self.pull_ast(*v, src).kind,
                x => unimplemented!("inner: {:?}", x),
            }
            PV::Char(x) => ValueKind::Char(x),
            // UInt is only an implementation detail, SPAIK code can't create or
            // interact with these values directly.
            PV::UInt(x) => panic!("Stray UInt: {}", x),
        };
        Value { kind, src: src.clone() }
    }

    pub unsafe fn pull_ast_norec(&self, v: PV, src: &Source) -> Value {
        #[derive(Debug)]
        enum Thing<'a> {
            Defer(PV, &'a Source),
            Cons(&'a Source),
        }
        use Thing::*;
        let mut stack = vec![Defer(v, src)];
        let mut ostack = vec![];
        while let Some(action) = stack.pop() {
            match action {
                Defer(v, src) => match v {
                    PV::Sym(sym) => ostack.push(Value { kind: ValueKind::Symbol(sym), src: src.clone() }),
                    PV::Nil => ostack.push(Value { kind: ValueKind::Nil, src: src.clone() }),
                    PV::Int(x) => ostack.push(Value { kind: ValueKind::Int(x), src: src.clone() }),
                    PV::Bool(x) => ostack.push(Value { kind: ValueKind::Bool(x), src: src.clone() }),
                    PV::Real(x) => ostack.push(Value { kind: ValueKind::Real(x), src: src.clone() }),
                    PV::Ref(p) => {
                        match (*p).match_ref() {
                            NkRef::Cons(nkgc::Cons { car, cdr }) => {
                                stack.push(Cons(src));
                                let src = self.mem.get_tag(p).unwrap_or(src);
                                stack.push(Defer(*car, src));
                                stack.push(Defer(*cdr, src));
                            },
                            NkRef::String(s) => ostack.push(Value { kind: ValueKind::String(s.clone()),
                                                                    src: src.clone() } ),
                            NkRef::PV(v) => stack.push(Defer(*v, src)),
                            x => unimplemented!("inner: {:?}", x),
                        }
                    }
                    PV::UInt(x) => panic!("Stray UInt: {}", x),
                    PV::Char(x) => panic!("Stray char: {}", x),
                },
                Cons(cons_src) => {
                    let car = ostack.pop().unwrap();
                    let cdr = ostack.pop().unwrap();
                    ostack.push(Value { kind: ValueKind::Cons(Box::new(car), Box::new(cdr)),
                                        src: cons_src.clone() })
                }
            }
        }
        debug_assert!(ostack.len() <= 1, "Multiple objects in output stack");
        ostack.pop().expect("No objects in output")
    }

    pub fn expand(&mut self, ast: &Value) -> Option<Result<Value, Error>> {
        ast.op()
           .and_then(|sym| self.macros.get(&sym.into()).copied())
           .map(|sym| {
               let args = ast.args().collect::<Vec<_>>();
               let mut asts = vec![];
               let pv = vm_call_with!(self, sym, args.len(), {
                   for arg in args.iter() {
                       let pv = self.mem.push_ast(arg);
                       asts.push(self.mem.make_extref(pv));
                   }
               });

               let out = unsafe { self.pull_ast(pv, &ast.src) };
               // FIXME: vm_call_with can error out, meaning this code won't
               //        run:
               for ast in asts.into_iter() {
                   let pv = ast.pv(self);
                   self.mem.untag_ast(pv);
               }

               Ok(out)
           })
    }

    pub fn set_macro(&mut self, macro_sym: SymID, fn_sym: SymID) {
        self.macros.insert(macro_sym.into(), fn_sym);
    }

    pub fn defun(&mut self,
                 sym: SymID,
                 args: PV,
                 ast: PV) -> Result<(), Error> {
        let mut cc = R8Compiler::new(self);
        let args = unsafe { pv_to_value(args, &Source::none()) };
        let ast = unsafe { pv_to_value(ast, &Source::none()) };
        let (spec, args) = cc.compile_fn(sym, &args, &ast)?;
        let code = cc.link()?;
        self.add_func(sym, code, spec, args);
        Ok(())
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
    pub fn unset_breakpoint(&mut self, idx: usize) -> Result<(), RuntimeError> {
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

    unsafe fn run_from_unwind(&mut self, offs: usize) -> Result<usize, Traceback> {
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
                  nargs: u16) -> Result<*mut r8c::Op, Error> {
        let idx = self.mem.stack.len() - nargs as usize - 1;
        let lambda_pv = self.mem.stack[idx];
        with_ref_mut!(lambda_pv, VLambda(lambda) => {
            lambda.args.check(lambda.name, nargs)?;
            let has_env = lambda.args.has_env();
            if !has_env {
                self.mem.stack.drain(idx..(idx+1)).for_each(drop); // drain gang
            }
            let sym = lambda.name;
            let pos = self.funcs
                          .get(&sym.into())
                          .ok_or_else(|| Error::from(
                              ErrorKind::UndefinedFunction {
                                  name: sym
                              }))
                          .map(|func| func.pos)?;
            self.call_pre(ip);
            self.frame = self.mem.stack.len()
                       - 2
                       - nargs as usize
                       - has_env as usize;
            Ok(self.ret_to(pos))
        }, Subroutine(subr) => {
            // SAFETY: The Subr trait is marked unsafe, read the associated
            //         safety documentation in Subr as to why this is safe. The
            //         alternative is to clone the stack slice, which is too
            //         expensive for us to do it for *every* Lisp->Rust call.
            let args = unsafe {
                let delta = (self.mem.stack.len() - nargs as usize) as isize;
                let ptr = self.mem.stack.as_ptr().offset(delta);
                slice::from_raw_parts(ptr, nargs as usize)
            };
            let dip = self.ip_delta(ip);
            let res = subr.call(self, args);
            self.mem.stack.drain(idx..).for_each(drop); // drain gang
            self.mem.push(res?);
            Ok(self.ret_to(dip))
        }, Continuation(cont) => {
            ArgSpec::normal(1).check(Builtin::Continuation.sym(), nargs)?;
            let cont_stack = cont.take_stack()?;

            let pv = self.mem.pop().unwrap();
            self.mem.stack.drain(idx..).for_each(drop); // drain gang

            // push state
            let dip = self.ip_delta(ip);
            let frame = self.frame;
            let stack = mem::replace(&mut self.mem.stack, cont_stack);
            self.mem.conts.push(stack);

            // call continuation
            self.mem.stack.push(pv);
            self.frame = cont.frame;
            let res = unsafe { self.run_from_unwind(cont.dip) };

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

            cont.put_stack(stack);

            res
        })
    }

    /**
     * Start running code from a point in program memory.
     *
     * NOTE: If the code isn't well-formed, i.e produces out-of-bounds jumps,
     * then you've yee'd your last haw.
     */
    unsafe fn run_from(&mut self, offs: usize) -> Result<usize, (usize, Error)> {
        let mut regs: Regs<2> = Regs::new();
        let mut ip = &mut self.pmem[offs] as *mut r8c::Op;
        use r8c::Op::*;
        let mut run = || loop {
            let op = &*ip;
            ip = ip.offset(1);
            match op {
                // List processing
                CAR() => {
                    let it = self.mem.pop()?;
                    with_ref_mut!(it, Cons(Cons { car, .. }) => {
                        self.mem.push(*car);
                        Ok(())
                    }).map_err(|e| e.op(Builtin::Car.sym()))?
                },
                CDR() => {
                    let it = self.mem.pop()?;
                    with_ref_mut!(it, Cons(Cons { cdr, .. }) => {
                        self.mem.push(*cdr);
                        Ok(())
                    }).map_err(|e| e.op(Builtin::Cdr.sym()))?
                },
                LIST(n) => self.mem.list(*n),
                VLIST() => {
                    let len = self.mem.pop()?.force_int() as u32;
                    self.mem.list(len);
                }
                CONS() => self.mem.cons_unchecked(),
                APPEND(n) => self.mem.append(*n)?,

                // Iterators
                NXIT(var) => {
                    let offset = (self.frame as isize) + (*var as isize);
                    let it = *self.mem.stack.as_ptr().offset(offset);
                    with_ref_mut!(it, Iter(it) => {
                        let elem = it.next()
                                     .unwrap_or_else(
                                         || PV::Sym(Builtin::IterStop.sym()));
                        self.mem.push(elem);
                        Ok(())
                    }).map_err(|e| e.op(Builtin::Next.sym()))?;
                }

                // Vectors
                VEC(n) => {
                    let len = self.mem.stack.len();
                    let vec = self.mem.stack
                                      .drain(len-(*n as usize)..)
                                      .collect::<Vec<_>>();
                    let ptr = self.mem.alloc::<Vec<PV>>();
                    ptr::write(ptr, vec);
                    self.mem.push(NkAtom::make_ref(ptr));
                }
                VPUSH() => {
                    let vec = self.mem.pop()?;
                    let elem = self.mem.pop()?;
                    with_ref_mut!(vec, Vector(v) => {
                        v.push(elem);
                        Ok(())
                    }).map_err(|e| e.op(Builtin::Push.sym()))?
                }
                VPOP() => {
                    let vec = self.mem.pop()?;
                    with_ref_mut!(vec, Vector(v) => {
                        let elem = v.pop().unwrap_or(PV::Nil);
                        self.mem.push(elem);
                        Ok(())
                    }).map_err(|e| e.op(Builtin::Pop.sym()))?;
                }
                VGET() => {
                    let op = Builtin::Get.sym();
                    let idx = match self.mem.pop()? {
                        PV::Int(x) => x as usize,
                        x => return Err(error!(TypeError,
                                               expect: Builtin::Integer.sym(),
                                               got: x.type_of()).op(op).argn(2))
                    };
                    let vec = self.mem.pop()?;
                    let elem = with_ref!(vec, Vector(v) => {
                        v.get(idx).ok_or(error!(IndexError, idx))
                    }).map_err(|e| e.op(op))?;
                    self.mem.push(*elem);
                }
                VSET() => {
                    // (set (get <vec> <idx>) <val>)
                    let op = Builtin::Set.sym();
                    let idx = match self.mem.pop()? {
                        PV::Int(x) => x as usize,
                        x => return Err(error!(TypeError,
                                               expect: Builtin::Integer.sym(),
                                               got: x.type_of()).op(op).argn(2))
                    };
                    let vec = self.mem.pop()?;
                    let val = self.mem.pop()?;
                    with_ref_mut!(vec, Vector(v) => {
                        if idx >= v.len() {
                            err!(IndexError, idx)
                        } else {
                            let p = &mut v[idx] as *mut PV;
                            *p = val;
                            // v[idx] = val;
                            Ok(())
                        }
                    }).map_err(|e| e.op(Builtin::Set.sym()))?;
                }
                LEN() => {
                    let li = self.mem.pop()?;
                    let len = with_ref!(li,
                                        Vector(v) => { Ok(v.len()) },
                                        String(s) => { Ok(s.len()) },
                                        Cons(_) => { Ok(li.iter().count()) })
                        .map_err(|e| e.op(Builtin::Len.sym()))?;
                    self.mem.push(PV::Int(len as i64));
                }

                // Value creation
                NIL() => self.mem.push(PV::Nil),
                CONSTREF(n) => self.consts[*n as usize].push_to(&mut self.mem),
                BOOL(i) => self.mem.push(PV::Bool(*i != 0)),
                CLZAV(nargs, nenv) => {
                    let start_idx = self.frame + *nargs as usize;
                    let end_idx = start_idx + *nenv as usize;
                    let lambda = self.mem.stack[self.frame];
                    let new_env = &self.mem.stack[start_idx..end_idx];
                    // Save environment
                    with_ref_mut!(lambda, VLambda(lambda) => {
                        for (dst, var) in lambda.locals.iter_mut().zip(new_env.iter()) {
                            *dst = *var;
                        }
                        Ok(())
                    })?;
                }
                CLZ(sym, nenv) => {
                    let to = self.mem.stack.len();
                    let from = to - *nenv as usize;
                    let locals: Vec<_> = self.mem.stack
                                                 .drain(from..to)
                                                 .collect();
                    let name = (*sym).into();
                    let args = self.funcs
                                   .get(sym)
                                   .ok_or(error_src!(Source::none(),
                                                     UndefinedFunction,
                                                     name))?.args;
                    self.mem.push_new(VLambda { name,
                                                locals,
                                                args });
                }

                // Math
                ADD() => ADD_OP(&mut self.mem.stack)?,
                SUB() => SUB_OP(&mut self.mem.stack)?,
                DIV() => DIV_OP(&mut self.mem.stack)?,
                MUL() => MUL_OP(&mut self.mem.stack)?,
                INC(v, d) => match self.mem.stack[self.frame + (*v as usize)] {
                    PV::Int(ref mut x) => *x += i64::from(*d),
                    PV::Real(ref mut x) => *x += f32::from(*d),
                    x => return Err(RuntimeError::new(format!("Cannot increment: {}", x)).into()),
                },
                DEC(v, d) => match self.mem.stack[self.frame + (*v as usize)] {
                    PV::Int(ref mut x) => *x -= i64::from(*d),
                    PV::Real(ref mut x) => *x -= f32::from(*d),
                    x => return Err(RuntimeError::new(format!("Cannot decrement: {}", x)).into()),
                },

                // Logic
                EQL() => EQL_OP(&mut self.mem.stack)?,
                EQLP() => EQLP_OP(&mut self.mem.stack)?,
                GT() => GT_OP(&mut self.mem.stack)?,
                GTE() => GTE_OP(&mut self.mem.stack)?,
                LT() => LT_OP(&mut self.mem.stack)?,
                LTE() => LTE_OP(&mut self.mem.stack)?,
                NOT() => {
                    let v = !bool::from(self.mem.pop()?);
                    self.mem.push(PV::Bool(v));
                },

                // Flow control
                JMP(d) => ip = ip.offset(*d as isize - 1),
                JT(d) => if bool::from(self.mem.pop()?) {
                    ip = ip.offset(*d as isize - 1);
                }
                JN(d) => if !bool::from(self.mem.pop()?) {
                    ip = ip.offset(*d as isize - 1);
                }
                JZ(d) => if self.mem.stack.pop() == Some(PV::Int(0)) {
                    ip = ip.offset(*d as isize - 1);
                }
                JNZ(d) => if self.mem.stack.pop() != Some(PV::Int(0)) {
                    ip = ip.offset(*d as isize - 1);
                }
                JV(mul, max) => {
                    let n = self.mem.pop()?.force_int() as isize;
                    let d = cmp::min((*mul as isize) * n, *max as isize);
                    ip = ip.offset(d);
                }
                VCALL(sym, nargs) => {
                    match self.funcs.get(sym) {
                        Some(func) => {
                            func.args.check((*sym).into(), *nargs)?;
                            let pos = func.pos;
                            self.call_pre(ip);
                            self.frame = self.mem.stack.len() - 2 - (*nargs as usize);
                            ip = self.ret_to(pos);
                        },
                        None => if let Some(idx) = self.get_env_global((*sym).into()) {
                            let var = self.mem.get_env(idx);
                            let sidx = self.mem.stack.len() - *nargs as usize;
                            // FIXME: This can be made less clunky by modifying
                            // op_clzcall so that it takes the callable as a parameter.
                            self.mem.stack.insert(sidx, var);
                            ip = self.op_clzcall(ip, *nargs)?;
                        } else {
                            return Err(ErrorKind::UndefinedFunction {
                                name: (*sym).into()
                            }.into())
                        }
                    };
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
                CLZCALL(nargs) => ip = self.op_clzcall(ip, *nargs)?,
                CALLCC(dip) => {
                    let dip = self.ip_delta(ip) as isize + *dip as isize;
                    let mut stack_dup = self.mem.stack.clone();
                    stack_dup.pop();
                    let cnt = self.mem.put(
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
                    let offset = (self.frame as isize) + (*var as isize);
                    self.mem
                        .push(*self.mem.stack.as_ptr().offset(offset))
                }
                STR(var) => {
                    let offset = (self.frame as isize) + (*var as isize);
                    *(self.mem.stack.as_mut_ptr().offset(offset)) = self.mem.pop()?
                },
                POP(n) => self.mem.popn(*n as usize),
                POPA(keep, pop) => {
                    let keep = *keep as usize;
                    let pop = *pop as usize;
                    let st = &mut self.mem.stack;
                    let top = st.len();
                    for (hi, lo) in (top - keep..top).zip(top - pop - keep..top) {
                        st[lo] = st[hi];
                    }
                    st.truncate(top - pop);
                }
                PUSH(n) => self.mem.push(PV::Int(i64::from(*n))),
                PUSHF(n) => self.mem.push(PV::Real(f32::from_bits(*n))),
                CHAR(c) => self.mem.push(PV::Char(char::from_u32_unchecked(*c))),
                SYM(id) => self.mem.push(PV::Sym((*id).into())),
                SAV(num) => regs.save(&mut self.mem, *num)?,
                RST() => regs.restore(&mut self.mem),
                TOP(d) => {
                    let top = self.mem.stack.len() - self.frame;
                    self.mem.push(PV::Int((top as i64) - (*d as i64)));
                }
                DUP() => self.mem.dup()?,
                CLZEXP() => self.mem.clz_expand(self.frame)?,

                // Static/env variables
                GET(var) => {
                    let val = self.mem.get_env(*var as usize);
                    self.mem.push(val);
                },
                SET(var) => {
                    let val = self.mem.pop()?;
                    self.mem.set_env(*var as usize, val);
                }

                HCF() => return Ok(()),
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

    pub fn dump_stack(&mut self) -> Result<(), Error> {
        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "stack:")?;
        if self.mem.stack.is_empty() {
            writeln!(stdout, "    (empty)")?;
        }
        for (idx, val) in self.mem.stack.iter().enumerate().rev() {
            let (idx, frame) = (idx as i64, self.frame as i64);
            write!(stdout, "{}", if idx == frame { " -> " } else { "    " })?;
            writeln!(stdout, "{}: {}", idx - frame, val)?;
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

    #[inline]
    pub fn set_frame(&mut self, nargs: u16) {
        let frame = self.frame;
        self.frame = self.mem.stack.len() - (nargs as usize);
        self.mem.push(PV::UInt(0));
        self.mem.push(PV::UInt(frame));
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
    pub fn call(&mut self, sym: SymID, args: impl AsArgs) -> Result<PV, Error> {
        Ok(vm_call_with!(self, sym, args.inner_nargs(), {
            args.inner_pusharg(&mut self.mem)?
        }))
    }

    pub fn call_spv(&mut self, sym: SymID, args: impl AsArgs) -> Result<SPV, Error> {
        let res = self.call(sym, args)?;
        Ok(self.mem.make_extref(res))
    }

    pub fn apply_spv(&mut self, f: SPV, args: impl AsArgs) -> Result<PV, Error> {
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

    pub fn raw_call(&mut self, sym: SymID, args: &[PV]) -> Result<PV, Error> {
        Ok(vm_call_with!(self, sym, args.len(), {
            for arg in args.iter() {
                self.mem.push(*arg);
            }
        }))
    }

    pub fn print_stack(&self) {
        self.mem.dump_stack();
    }

    pub fn get_code(&self) -> Vec<r8c::Op> {
        self.pmem.clone()
    }

    pub fn print_fmt(&mut self, args: fmt::Arguments) -> Result<(), Error> {
        self.stdout.lock().unwrap().write_fmt(args)?;
        Ok(())
    }

    pub fn print(&mut self, obj: &dyn Display) -> Result<(), Error> {
        self.print_fmt(format_args!("{}", obj))
    }

    pub fn println(&mut self, obj: &dyn Display) -> Result<(), Error> {
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

    #[cfg(feature = "repl")]
    pub fn dump_all_code(&self) -> Result<(), Error> {
        let mut funks = self.funcs.iter().map(|(k, v)| ((*k).into(), v.pos)).collect::<Vec<_>>();
        funks.sort_by_key(|(_, v)| *v);
        for funk in funks.into_iter().map(|(u, _)| u) {
            self.dump_fn_code(funk)?
        }
        Ok(())
    }

    #[cfg(feature = "repl")]
    pub fn dump_fn_code(&self, mut name: SymID) -> Result<(), Error> {
        use colored::*;

        lazy_static! {
            static ref EMPTY_MAP: FnvHashMap<u32, Lbl> = FnvHashMap::default();
        }
        if let Some(mac_fn) = self.macros.get(&name.into()) {
            name = *mac_fn;
        }
        let func = self.funcs.get(&name.into()).ok_or("No such function")?;
        let labels = self.func_labels.get(&name)
                                     .unwrap_or(&EMPTY_MAP);
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
                             vec![labels.get(&((pos + delta - start) as u32))
                                        .map(|lbl| format!("{}", lbl))
                                        .unwrap_or(format!("{}", delta))
                                        .yellow().to_string()]))
            }
            let sym_name = |sym: SymIDInt| self.sym_name(sym.into()).to_string();
            Some((op.name().to_lowercase(), match op {
                VCALL(name, args) => vec![sym_name(name), args.to_string()],
                SYM(sym) => vec![sym_name(sym)],
                CLZ(sym, env) => vec![sym_name(sym), env.to_string()],
                _ => return None
            }))
        };

        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "{}({}):",
                 self.sym_name(name).cyan().bold(),
                 func.args)?;
        for i in start..start+(func.sz as isize) {
            let op = self.pmem[i as usize];
            if let Some(s) = labels.get(&(((i as isize) - start) as u32)) {
                writeln!(stdout, "{}:", s.to_string().yellow().bold())?;
            }
            let (name, args) = fmt_special(i as isize, op).unwrap_or(
                (op.name().to_lowercase(),
                 op.args().iter().map(|v| v.to_string()).collect())
            );
            writeln!(stdout, "    {} {}",
                     name.blue().bold(),
                     args.join(", "))?;
        }

        Ok(())
    }

    #[cfg(feature = "repl")]
    pub fn dump_macro_tbl(&self) -> Result<(), Error> {
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

    #[cfg(feature = "repl")]
    pub fn dump_symbol_tbl(&self) -> Result<(), Error> {
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

    #[cfg(feature = "repl")]
    pub fn dump_env_tbl(&self) -> Result<(), Error> {
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

    #[cfg(feature = "repl")]
    pub fn dump_fn_tbl(&self) -> Result<(), Error> {
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

    pub fn freeze(&self) -> LispModule {
        let mut exports = Vec::new();
        exports.extend(self.funcs.iter()
                       .map(|(&name, f)| Export::new(ExportKind::Func,
                                                     name.into(),
                                                     f.pos.try_into().unwrap())));
        LispModule::new(&self.pmem, &self.mem.symdb, &self.consts, vec![], exports)
    }
}
