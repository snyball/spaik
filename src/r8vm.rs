//! SPAIK R8 Virtual Machine

#[cfg(feature = "repl")]
use comfy_table::Table;

use crate::{
    ast::{Value, ValueKind},
    chasm::{ASMOp, ChASMOpName, Lbl, ASMPV},
    compile::{pv_to_value, Builtin, Linked, R8Compiler},
    error::{Error, ErrorKind, Source},
    fmt::LispFmt,
    module::{LispModule, Export, ExportKind},
    nuke::*,
    nkgc::{Arena, Cons, SymID, SymIDInt, VLambda, PV, SPV, self},
    perr::PResult,
    sexpr_parse::Parser,
    subrs::{IntoLisp, Subr},
    sym_db::SymDB,
};
use fnv::FnvHashMap;
use std::{io, borrow::Cow, cmp, collections::HashMap, convert::TryInto, fmt::{self, Debug, Display}, fs::File, io::prelude::*, mem, ptr, slice, sync::Mutex};

chasm_def! {
    r8c:

    // List processing
    CONS(),
    APPEND(num: u32),
    LIST(num: u32),
    VLIST(),
    CAR(),
    CDR(),
    SETCAR(),
    SETCDR(),

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
    JSYM(sym: SymIDInt),
    JNSYM(sym: SymIDInt),
    CALL(dip: i32, nargs: u16),
    VCALL(func: SymIDInt, nargs: u16),
    // TODO: APPLY()
    CLZCALL(nargs: u16),
    SYSCALL(idx: u16),
    RET(),
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

#[derive(Debug, Clone, PartialEq)]
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

macro_rules! stack_ref_op {
    ( [ $m:pat ] $type:ty => $action:block ) => {
        |st: &mut Vec<$type>| -> Result<(), Error> {
            let v = st.pop().expect(
                "Empty stack when running op, likely code-gen failure"
            );
            if let PV::Ref(r) = v {
                unsafe {
                    if let $m = (*r).match_ref() {
                        st.push($action);
                    } else {
                        return Err(RuntimeError::new(format!(
                            "Expected {} but got {:?}",
                            stringify!($m),
                            (*r).type_of()
                        )).into());
                    }
                }
            } else {
                return Err(RuntimeError::new(format!(
                    "Expected PV::Ref({}) but got {:?}",
                    stringify!($m),
                    v
                )).into());
            }
            Ok(())
        }
    };
}

pub struct SysFn {
    pub nargs: u16,
    pub name: &'static str,
    f: fn(&mut R8VM, &[PV]) -> Result<PV, Error>,
}

impl SysFn {
    // FIXME: Implementing Fn isn't in Rust stable yet, so I can't just do sys_fn(stack),
    //        change this into an `impl Fn<_> for SysFn` later on.
    fn call(&self, vm: &mut R8VM) -> Result<(), Error> {
        let slen = vm.mem.stack.len();
        if slen < (self.nargs as usize) {
            return Err(RuntimeError::new(format!(
                "System call expected {} args, but got {}.",
                self.nargs,
                slen
            )).into());
        }
        self.call_unchecked(vm)
    }

    /// Works like call, but will panic if there aren't enough arguments
    /// on the stack.
    fn call_unchecked(&self, vm: &mut R8VM) -> Result<(), Error> {
        let top = vm.mem.stack.len() - (self.nargs as usize);
        let args = vm.mem.stack.drain(top..).collect::<Vec<PV>>();
        let res = (self.f)(vm, &args[..])?;
        vm.mem.stack.push(res);
        Ok(())
    }
}

pub fn mk_sysfn_lookup(funcs: &[SysFn]) -> HashMap<&str, &SysFn> {
    funcs.iter().map(|f| (f.name, f)).collect()
}

pub fn mk_sysfn_idx_lookup(funcs: &[SysFn]) -> HashMap<&str, i64> {
    funcs.iter()
         .enumerate()
         .map(|(i, f)| (f.name, i as i64))
         .collect()
}

pub fn mk_default_sysfn_idx_lookup() -> HashMap<&'static str, i64> {
    mk_sysfn_idx_lookup(&SYSTEM_FUNCTIONS)
}

macro_rules! sysfn_pat {
    ( $arg:ident : Any ) => {
        $arg
    };
    ( $arg:ident : $type:ident ) => {
        PV::$type($arg)
    };
}

macro_rules! sysfn_ret {
    ( $res:expr, Any ) => {
        $res
    };
    ( $res:expr, ) => {
        PV::Nil
    };
    ( $res:expr, Nil ) => {
        PV::Nil
    };
    ( $res:expr, $otype:ident ) => {
        PV::$otype($res)
    };
}

macro_rules! defsysfn {
    ( $( use $vm:ident fn $name:ident ( $( $arg:ident : $type:ident ),* ) $(-> $otype:ident)* $body:block )* ) => {
        pub const SYSTEM_FUNCTIONS: [SysFn; count_args!($($name),*)] = sysfn!(
            $( use $vm fn $name ( $( $arg : $type ),* ) $(-> $otype)* $body )*
        );
    }
}

macro_rules! sysfn {
    ( $( use $vm:ident fn $name:ident ( $( $arg:ident : $type:ident ),* )
         $(-> $otype:ident)*
         $body:block
    )* ) =>
    {
        [
            $(SysFn {
                nargs: count_args!($($arg),*),
                name: concat!("sys::", stringify!($name)),
                #[allow(unused_variables)]
                f: |$vm, args: &[PV]| -> Result<PV, Error> {
                    #[allow(clippy::match_ref_pats, unused_variables)]
                    let res: Result<_, Error> = match args {
                        #[warn(unused_variables)]
                        &[$(sysfn_pat!($arg : $type)),*] => { $body }
                        x => return Err(RuntimeError::new(
                            format!("Illegal arguments for syscall: (sys::{} {})",
                                    stringify!($name).to_string().replace("_", "-"), {
                                        x.iter()
                                         .map(|v| v.lisp_to_string(&$vm.mem))
                                         .collect::<Vec<_>>()
                                         .join(" ")
                                    } )).into()),
                    };
                    #[allow(unreachable_code)]
                    match res {
                        Ok(_res) => Ok(sysfn_ret!(_res, $($otype)*)),
                        Err(e) => Err(e)
                    }
                }
            }),*
        ]
    }
}

#[macro_export]
macro_rules! spaik {
    ($vm:expr => ( $fn:expr, ($call:expr),+ )) =>
        { $vm.call($fn, &[($call.into()),+]) };
    ($vm:expr => ( $fn:literal, ($call:expr),+ )) =>
        { $vm.call_s($fn, &[($call.into()),+]) };
    ($vm:expr => ( $fn:expr )) =>
        { $vm.call($fn, &[]) };
    ($vm:expr => ( $fn:literal )) =>
        { $vm.call_s($fn, &[]) };
    ($vm:expr => $val:expr) =>
        { $vm.getvar($fn) };
    ($vm:expr => ( $val:literal )) =>
        { $vm.getvar_s($fn) };
}

fn tostring(vm: &R8VM, x: PV) -> String {
    match x {
        PV::Ref(y) => match unsafe { (*y).match_ref() } {
            NkRef::String(s) => s.clone(),
            _ => x.lisp_to_string(&vm.mem),
        }
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
        pub struct $name();

        unsafe impl Subr for $name {
            fn call(&mut $self, $vm: &mut R8VM, $args: &[PV]) -> Result<PV, Error> $body
            fn name(&self) -> &'static str { $name_s }
            fn into_subr(self) -> Box<dyn Subr> { Box::new(self) }
        }

        impl From<$name> for Box<dyn $crate::subrs::Subr> {
            fn from(x: $name) -> Self {
                Box::new(x)
            }
        }
    };

    (fn $name:ident(&mut $self:ident, $vm:ident : &mut R8VM, $args:ident : &[PV])
                    -> Result<PV, Error> $body:block) => {
        subr!(fn $name[stringify!($name)](&mut $self, $vm : &mut R8VM, $args : &[PV])
                                          -> Result<PV, Error> $body);
    };

    (fn $name:ident[$name_s:literal](&mut $self:ident, $vm:ident : &mut R8VM, $args:ident : &[PV])
                    -> Result<PV, Error> $body:block) => {
        subr!(fn $name[$name_s](&mut $self, $vm : &mut R8VM, $args : &[PV])
                                -> Result<PV, Error> $body);
    };

    (fn $name:ident(&mut $self:ident, $vm:ident : &mut R8VM, args: ($($arg:ident),*)) -> Result<PV, Error> $body:block) => {
        subr!(fn $name(&mut $self, $vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            subr_args!(($($arg),*) $self $vm args {
                $body
            })
        });
    };

    (fn $name:ident[$name_s:literal](&mut $self:ident, $vm:ident : &mut R8VM, args: ($($arg:ident),*)) -> Result<PV, Error> $body:block) => {
        subr!(fn $name[$name_s](&mut $self, $vm: &mut R8VM, args: &[PV]) -> Result<PV, Error> {
            subr_args!(($($arg),*) $self $vm args {
                $body
            })
        });
    }
}

macro_rules! subr_args {
    (($($arg:ident),*) $self:ident $vm:ident $args:ident $body:block) => {
        match &$args[..] {
            [$($arg),*] => {
                $body
            },
            _ => err!(ArgError,
                      expect: ArgSpec::normal(count_args!($($arg),*)),
                      got_num: $args.len() as u32,
                      op: $vm.sym_id($self.name()))
        }
    };
}

macro_rules! std_subrs {
    ($(fn $name:ident($($inner:tt)*) -> Result<PV, Error> $body:block)*) => {
        $(subr!(fn $name($($inner)*) -> Result<PV, Error> $body);)*
    };
}

// TODO: Replace the whole SYSCALL machinery with Subr
#[allow(non_camel_case_types)]
mod sysfns {
    use std::{fmt::Write, convert::Infallible};

    use crate::{subrs::{Subr, IntoLisp}, nkgc::PV, error::Error, fmt::{LispFmt, FmtWrap}};
    use super::{R8VM, tostring, ArgSpec};

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
            let mut out = String::new();
            for val in args.iter() {
                with_ref!(*val, String(s) => {
                    write!(&mut out, "{s}").unwrap();
                    Ok(())
                }).or_else(|_| -> Result<(), Infallible> {
                    write!(&mut out, "{}", FmtWrap { val, db: vm }).unwrap();
                    Ok(())
                }).unwrap();
            }
            out.into_pv(&mut vm.mem)
        }

        fn iter(&mut self, vm: &mut R8VM, args: (x)) -> Result<PV, Error> {
            x.make_iter()?.into_pv(&mut vm.mem)
        }
    }
}

defsysfn! {
    use _vm fn pow(x: Int, exp: Int) -> Int {
        Ok(x.pow(exp as u32))
    }

    use _vm fn modulo(a: Int, base: Int) -> Int {
        Ok(a % base)
    }

    use vm fn set_macro(macro_name: Sym, fn_name: Sym) {
        vm.set_macro(macro_name, fn_name);
        Ok(())
    }

    use vm fn concat_symbols(a: Sym, b: Sym) -> Sym {
        let id: SymID = vm.mem
                          .symdb
                          .put(format!("{}{}", vm.sym_name(a), vm.sym_name(b)));
        Ok(id)
    }

    use vm fn make_symbol(a: Any) -> Sym {
        Ok(vm.mem.symdb.put(tostring(vm, a)))
    }

    use vm fn read(text: Any) -> Any {
        vm.read(&tostring(vm, text))?;
        vm.mem.pop()
    }

    use vm fn load(lib: Sym) -> Sym {
        vm.load(lib)
    }

    use vm fn trace_opcodes(enabled: Bool) {
        vm.set_debug_mode(enabled);
        Ok(())
    }

    use vm fn macroexpand(ast: Any) -> Any {
        let mut ast = unsafe { pv_to_value(ast, &Source::none()) };
        let v = vm.macroexpand(&mut ast)?;
        vm.push_ast(v);
        vm.mem.pop()
    }

    use vm fn dump_macro_tbl() {
        featurefn!("repl", vm.dump_macro_tbl()?)
    }

    use vm fn dump_sym_tbl() {
        featurefn!("repl", vm.dump_symbol_tbl()?)
    }

    use vm fn dump_env_tbl() {
        featurefn!("repl", vm.dump_env_tbl()?)
    }

    use vm fn dump_fn_tbl() {
        featurefn!("repl", vm.dump_fn_tbl()?)
    }

    use vm fn disassemble(func: Sym) {
        featurefn!("repl", vm.dump_fn_code(func)?)
    }

    use vm fn exit(status: Sym) {
        // Written in a strange way in order to assist the type-checker.
        Err(Error { ty: ErrorKind::Exit { status },
                    src: None })?; // boom
        Ok(())
    }

    use vm fn type_of(obj: Any) -> Sym {
        Ok(obj.type_of())
    }

    use vm fn dump_gc_stats() {
        vm.print_fmt(format_args!("{:?}", vm.mem.stats()))?;
        vm.println(&"")?;
        Ok(())
    }

    use vm fn dump_stack() {
        vm.dump_stack()?;
        Ok(())
    }
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
            err!(ArgError,
                 expect: *self,
                 got_num: nargs.into(),
                 op: fn_sym)
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
    sysfns: FnvHashMap<SymIDInt, usize>,

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
            mem: Default::default(),
            globals: Default::default(),
            breaks: Default::default(),
            macros: Default::default(),
            funcs: Default::default(),
            func_labels: Default::default(),
            sysfns: Default::default(),
            stdout: Mutex::new(Box::new(io::stdout())),
            stdin: Mutex::new(Box::new(io::stdin())),
            debug_mode: false,
            frame: Default::default(),
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

const CAR_OP: StackOpFn<PV> =
    stack_ref_op!([NkRef::Cons(Cons {car, ..})] PV => { *car });
const CDR_OP: StackOpFn<PV> =
    stack_ref_op!([NkRef::Cons(Cons {cdr, ..})] PV => { *cdr });

#[derive(Default)]
struct Regs {
    vals: [PV; 16],
    idx: u8,
}

impl Regs {
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

pub trait Args {
    fn push(self, mem: &mut Arena) -> Result<(), Error>;
    fn nargs(&self) -> usize;
}

impl Args for &[PV] {
    fn push(self, mem: &mut Arena) -> Result<(), Error> {
        for arg in self.iter().copied() {
            mem.push(arg);
        }
        Ok(())
    }

    fn nargs(&self) -> usize {
        self.len()
    }
}

impl<const N: usize> Args for &[PV; N] {
    fn push(self, mem: &mut Arena) -> Result<(), Error> {
        for arg in self.iter().copied() {
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
            where $($arg: IntoLisp),*
        {
            fn push(self, mem: &mut Arena) -> Result<(), Error> {
                #[allow(non_snake_case)]
                let ($($arg),*,) = self;
                $(
                    #[allow(non_snake_case)]
                    let $arg = $arg.into_pv(mem)?;
                    mem.push($arg);
                )*
                Ok(())
            }

            fn nargs(&self) -> usize {
                count_args!($($arg),*)
            }
        }
    };
}

impl Args for () {
    fn push(self, _mem: &mut Arena) -> Result<(), Error> { Ok(()) }
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

impl R8VM {
    pub fn new() -> R8VM {
        let mut vm = R8VM {
            pmem: vec![r8c::Op::HCF()],
            ..Default::default()
        };

        for (i, sysfn) in SYSTEM_FUNCTIONS.iter().enumerate() {
            let sym = vm.mem.symdb.put(sysfn.name.replace('_', "-"));
            vm.sysfns.insert(sym.id, i);
        }

        vm.funcs.insert(Builtin::HaltFunc.sym().into(), Func {
            pos: 0,
            sz: 1,
            args: ArgSpec::none()
        });

        macro_rules! addfn {
            ($name:ident) => {
                let sym = vm.mem.put_sym(stringify!($name));
                vm.set(sym, sysfns::$name().into_subr()).unwrap();
            };
        }


        addfn!(println);
        addfn!(print);
        addfn!(string);
        addfn!(eval);
        addfn!(read);
        addfn!(concat);
        addfn!(iter);

        vm
    }

    pub fn minimize(&mut self) {
        self.mem.minimize();
        self.pmem.shrink_to_fit();
        self.consts.shrink_to_fit();
        self.globals.shrink_to_fit();
        self.breaks.shrink_to_fit();
        self.funcs.shrink_to_fit();
        self.func_labels.shrink_to_fit();
        self.sysfns.shrink_to_fit();
    }

    pub fn set<T: IntoLisp>(&mut self, var: SymID, obj: T) -> Result<(), Error> {
        let pv = obj.into_pv(&mut self.mem)?;
        let idx = self.mem.push_env(pv);
        self.globals.insert(var, idx);
        Ok(())
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

    pub fn get_func(&self, name: SymID) -> Option<&Func> {
        self.funcs.get(&name.id)
    }

    pub fn add_func(&mut self, name: SymID, code: Linked, args: ArgSpec) {
        let (asm, labels, consts) = code;
        self.funcs.insert(name.id, Func {
            pos: self.pmem.len(),
            sz: asm.len(),
            args
        });
        self.func_labels.insert(name, labels);
        self.add_code(asm, Some(consts));
    }

    pub fn load(&mut self, lib: SymID) -> Result<SymID, Error> {
        let sym_name = self.sym_name(lib).to_string();
        let err = ErrorKind::ModuleLoadError { lib };
        let mut file = File::open(format!("lisp/{}.lisp", &sym_name))
            .map_err(|_| err.clone())?;
        let mut src = String::new();
        file.read_to_string(&mut src).map_err(|_| err)?;
        let ast = Parser::parse(self, &src)?;
        let mut cc = R8Compiler::new(self);
        cc.compile_top(true, &ast)?;
        let (mut asm, lbls, consts) = cc.link()?;
        asm.push(r8c::Op::RET());
        let fn_sym = self.mem.symdb.put(format!("<Σ>::{}", sym_name));
        self.add_func(fn_sym, (asm, lbls, consts), ArgSpec::none());
        Ok(fn_sym)
    }

    pub fn consts_top(&self) -> usize {
        self.consts.len()
    }

    pub fn get_env_global(&self, name: SymID) -> Option<usize> {
        self.globals.get(&name).copied()
    }

    pub fn get_sysfn(&self, name: SymID) -> Option<usize> {
        self.sysfns.get(&name.id).copied()
    }

    /// Reads LISP code into an AST.
    pub fn read(&mut self, lisp: &str) -> PResult<()> {
        let ast = Parser::parse(self, lisp)?;
        self.push_ast(&ast);
        Ok(())
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
                    consts: Option<Vec<NkSum>>) {
        let const_rel = self.consts.len() as u32;
        for op in code.iter_mut() {
            if let r8c::Op::CONSTREF(ref mut i) = *op {
                *i += const_rel;
            }
        }
        self.pmem.extend(code);
        if let Some(consts) = consts {
            self.consts.extend(consts);
        }
    }

    /**
     * Add some code and run it, returning the result.
     *
     * SAFETY: Safe as long as `code` is well-formed.
     */
    pub unsafe fn add_and_run(&mut self,
                              code: Vec<r8c::Op>,
                              consts: Option<Vec<NkSum>>) -> Result<PV, Error> {
        let c_start = self.pmem.len();
        let prev_top = self.mem.stack.len();
        self.add_code(code, consts);
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
        let (asm, _, consts) = cc.link()?;
        unsafe {
            self.add_and_run(asm, Some(consts))
        }
    }

    pub fn eval(&mut self, expr: &str) -> Result<PV, Error> {
        let ast = Parser::parse(self, expr)?;
        let mut cc = R8Compiler::new(self);
        // cc.estack.push(Env::empty());
        cc.compile_top(true, &ast)?;
        let globs = cc.globals()
                      .map(|v| v.map(|(u, v)| (*u, *v))
                                .collect::<Vec<_>>());
        let (asm, _, consts) = cc.link()?;
        if let Some(globs) = globs {
            for (name, idx) in globs {
                self.globals.insert(name, idx);
            }
        }
        unsafe {
            self.add_and_run(asm, Some(consts))
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
            PV::UInt(x) => panic!("Stray UInt: {}", x),
            PV::Char(x) => panic!("Stray char: {}", x),
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
           .and_then(|sym| self.macros.get(&sym.id).copied())
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
                   self.mem.untag_ast(unsafe { ast.pv() });
               }

               Ok(out)
           })
    }

    pub fn set_macro(&mut self, macro_sym: SymID, fn_sym: SymID) {
        self.macros.insert(macro_sym.id, fn_sym);
    }

    pub fn defun(&mut self,
                 sym: SymID,
                 args: PV,
                 ast: PV) -> Result<(), Error> {
        let mut cc = R8Compiler::new(self);
        let args = unsafe { pv_to_value(args, &Source::none()) };
        let ast = unsafe { pv_to_value(ast, &Source::none()) };
        let spec = cc.compile_fn(sym, &args, &ast)?;
        let code = cc.link()?;
        self.add_func(sym, code, spec);
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
     * Unwind the stack into a Traceback.
     *
     * # Arguments
     *
     * - `ip` : The instruction IP from which to unwind.
     * - `err` : The error to initialize the Traceback with
     */
    pub fn stack_unwind(&mut self, mut ip: usize, err: Error) -> Traceback {
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
                name = Builtin::Unknown.sym().id;
                (0, 0)
            } else {
                let spec = func.args;
                (spec.env as usize,
                 spec.sum_nargs() as usize)
            };

            let frame = self.frame;
            let args = self.mem.stack.drain(frame..frame+nargs).collect();
            frames.push(TraceFrame { args,
                                     func: name.into(),
                                     src: Source::none() });

            self.mem.stack.drain(frame..frame+nenv).for_each(drop);
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

    unsafe fn run_from_unwind(&mut self, offs: usize) -> Result<usize,
                                                                Traceback> {
        match self.run_from(offs) {
            Ok(ip) => Ok(ip),
            Err((ip, e)) => Err(self.stack_unwind(ip, e)),
        }
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
                self.mem.stack.drain(idx..(idx+1)).for_each(drop);
            }
            let sym = lambda.name;
            let pos = self.funcs
                          .get(&sym.id)
                          .ok_or_else(|| Error::from(
                              ErrorKind::UndefinedFunction {
                                  name: sym
                              }))
                          .map(|func| func.pos)?;
            self.call_pre(ip);
            self.frame =
                self.mem.stack.len()
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
            self.mem.stack.drain(idx..).for_each(drop);
            self.mem.push(res?);
            Ok(self.ret_to(dip))
        })
    }

    /**
     * Start running code from a point in program memory.
     *
     * NOTE: If the code isn't well-formed, i.e produces out-of-bounds jumps,
     * then you've yee'd your last haw.
     */
    unsafe fn run_from(&mut self, offs: usize) -> Result<usize, (usize, Error)> {
        let mut regs = Regs::default();
        let mut ip = &mut self.pmem[offs] as *mut r8c::Op;
        use r8c::Op::*;
        let mut run = || loop {
            let op = &*ip;
            ip = ip.offset(1);
            if self.debug_mode {
                vmprintln!(self, "{}", op);
            }
            match op {
                // List processing
                CAR() => CAR_OP(&mut self.mem.stack)?,
                CDR() => CDR_OP(&mut self.mem.stack)?,
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
                                     .unwrap_or(PV::Sym(Builtin::IterStop.sym()));
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
                        x => return err!(TypeError,
                                         expect: Builtin::Integer.sym(),
                                         got: x.type_of(),
                                         argn: 2,
                                         op)
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
                        x => return err!(TypeError,
                                         expect: Builtin::Integer.sym(),
                                         got: x.type_of(),
                                         argn: 2,
                                         op)
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
                    let name = SymID { id: *sym };
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
                    let pos = match self.funcs.get(sym) {
                        Some(func) => {
                            func.args.check((*sym).into(), *nargs)?;
                            func.pos
                        },
                        // TODO: Add source information when this becomes available
                        //       during run-time.
                        None => return Err(ErrorKind::UndefinedFunction {
                            name: SymID { id: *sym }
                        }.into())
                    };
                    self.call_pre(ip);
                    self.frame = self.mem.stack.len() - 2 - (*nargs as usize);
                    ip = self.ret_to(pos);
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
                SYSCALL(n) => {
                    let dip = self.ip_delta(ip);
                    let res = SYSTEM_FUNCTIONS[*n as usize].call(self);
                    // System functions may re-allocate pmem, which will invalidate
                    // the `ip` pointer. Therefore we compute `dip` and reset `ip` after
                    // calling the system function.
                    ip = self.ret_to(dip);
                    res?;
                }
                CLZCALL(nargs) => ip = self.op_clzcall(ip, *nargs)?,

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

                x => { unimplemented!("{}", x) }
            }
            self.mem.collect();

            if self.debug_mode {
                self.dump_stack()?;
                vmprintln!(self, "");
            }
        };

        let res = run();
        let dip = self.ip_delta(ip);
        match res {
            Ok(_) => Ok(dip),
            Err(e) => Err((dip, e))
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
    pub fn call<A>(&mut self, sym: SymID, args: A) -> Result<PV, Error>
        where A: Args
    {
        Ok(vm_call_with!(self, sym, args.nargs(), { args.push(&mut self.mem)? }))
    }

    pub fn call_spv<A>(&mut self, sym: SymID, args: A) -> Result<SPV, Error>
        where A: Args
    {
        let res = self.call(sym, args)?;
        Ok(self.mem.make_extref(res))
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
    pub fn dump_fn_code(&self, mut name: SymID) -> Result<(), Error> {
        use colored::*;

        lazy_static! {
            static ref EMPTY_MAP: FnvHashMap<u32, Lbl> = FnvHashMap::default();
        }
        if let Some(mac_fn) = self.macros.get(&name.id) {
            name = *mac_fn;
        }
        let func = self.funcs.get(&name.id).ok_or("No such function")?;
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
                SYSCALL(idx) => vec![SYSTEM_FUNCTIONS[idx as usize]
                                     .name.to_string()],
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
            table.add_row(vec![name, &id.id.to_string()]);
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
        exports.extend(self.funcs.iter().map(|(&name, f)| Export::new(ExportKind::Func,
                                                                      name.into(),
                                                                      f.pos.try_into().unwrap())));
        LispModule::new(&self.pmem, &self.mem.symdb, &self.consts, vec![], exports)
    }
}
