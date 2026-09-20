//! The Rodent VM

#[cfg(feature = "extra")]
use comfy_table::Table;
#[cfg(feature = "math")]
use glam::{Mat2, Mat3};

#[cfg(feature = "modules")]
use crate::module::{LispModule, Export, ExportKind};
use crate::{
    ast::{Excavator, Visitor}, builtins::Builtin, chasm::{ASMOp, ChASMOpName, Lbl, LblMap, ASMPV}, comp::{R8Compiler, SourceList}, error::{Error, ErrorKind, LineCol, Meta, OpName, Result, Source, SourceFileName, SyntaxErrorKind}, fmt::LispFmt, limits, nkgc::{self, Arena, Cons, ConsOption, Int, Lambda, NonRef, QuasiMut, SymID, PV, SPV}, nuke::*, opt::Optomat, reader::{Sexper, Sexpert}, string_parse::string_parse, subrs::{BoxSubr, FromLisp, Lispify, Subr}, swym::{self, SymRef}, tok::Token, tokit, AsSym, IntoLisp};
use crate::utils::{HMap, HSet};
use std::{alloc::{alloc, dealloc, realloc, Layout}, any::{type_name, Any, TypeId}, borrow::Cow, cmp::{self, Ordering}, collections::hash_map::Entry, convert::{Infallible, TryInto}, fmt::{self, Debug, Display}, fs, io::{self, prelude::*}, marker::PhantomData, mem::{self, replace, take}, ops::{self, Index, IndexMut}, path::{Path, PathBuf}, ptr::{self, addr_of_mut, NonNull}, sync::{atomic::AtomicU32, Arc, Mutex}};
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
    CTH(dip: i32),
    CTHPOP(),
    UWND(),
    YEET(),
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
    CLZ(pos: u32, nenv: u16),
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
    MUL(),

    // Meta
    MXP(),
    PRT(),
    EVL()
}

pub type VmId = u32;

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

pub fn sysrand_impl() -> Result<f32> {
    let mut urandom = fs::File::open("/dev/urandom")?;
    let mut buf = [0; 4];
    urandom.read_exact(&mut buf)?;
    let mut uint = u32::from_ne_bytes(buf);
    uint &= 0x00FFFFFF;
    Ok(uint as f32 / 16777216.0)
}

mod sysfns;

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

    pub const fn is_valid_num(&self, nargs: usize) -> bool {
        if self.has_body() && nargs >= self.nargs as usize {
            return true;
        }
        (nargs == self.nargs as usize) ||
        (!self.has_body() && self.has_opt() &&
         nargs >= self.nargs as usize && nargs <= (self.nargs + self.nopt) as usize)
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

    pub fn check(&self, nargs: impl Into<usize> + Clone) -> Result<()> {
        if self.is_valid_num(nargs.clone().into()) {
            Ok(())
        } else {
            Err(error!(ArgError,
                       expect: *self,
                       got_num: nargs.clone().into() as u32))
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Func {
    pub(crate) pos: IPtr<r8c::Op>,
    pub(crate) sz: u32,
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

#[derive(Debug)]
pub struct DevNull;

impl io::Write for DevNull {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(not(feature = "no-threading"))]
pub trait OutStream: io::Write + Debug + Send {}
#[cfg(not(feature = "no-threading"))]
impl<T> OutStream for T where T: io::Write + Debug + Send {}

pub type ObjMethod = unsafe fn(*mut u8, &mut R8VM, &[PV]) -> Result<PV>;

#[derive(Clone, Default)]
pub struct VmStats {
    instructions: usize,
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct Guard {
    dip: IP,
    sym: Option<usize>,
    top: usize,
    frame: usize,
}

pub type VmStdout = Arc<Mutex<Box<dyn OutStream>>>;

#[derive(Clone, Default, Debug)]
#[cfg_attr(feature = "cli", derive(clap::Parser))]
pub struct VmDebugOpts {
    #[cfg_attr(feature = "cli", arg(long))]
    pub show_opcodes: bool,
    #[cfg_attr(feature = "cli", arg(long))]
    pub show_stack_on_ret: bool,
    #[cfg_attr(feature = "cli", arg(long))]
    pub show_frames: bool,
    #[cfg(feature = "gc-assertions")]
    #[cfg_attr(feature = "cli", arg(long))]
    pub assert_gc_invariants: bool,
}

#[derive(Clone)]
pub struct R8VM {
    /// Memory
    pub(crate) pmem: PMemT,
    pub mem: Arena,
    pub(crate) globals: HMap<SymID, usize>,
    resources: HMap<TypeId, usize>,
    pub(crate) trace_counts: HMap<SymID, usize>,
    tok_tree: tokit::Fragment,
    reader_macros: HMap<String, SymID>,
    stats: VmStats,

    // Named locations/objects
    breaks: HMap<usize, r8c::Op>,
    macros: HMap<SymID, SymID>,
    pub(crate) funcs: HMap<SymID, Func>,
    func_labels: HMap<SymID, HMap<u32, Lbl>>,
    pub(crate) labels: LblMap,
    func_arg_syms: HMap<SymID, Vec<SymID>>,
    pub(crate) srctbl: SourceList,
    catch: Vec<Guard>,
    libs: HMap<SymID, (PathBuf, fs::Metadata)>,

    obj_methods: HMap<(TypeId, SymID), ObjMethod>,

    stdout: Arc<Mutex<Box<dyn OutStream>>>,

    debug_mode: VmDebugOpts,

    frame: usize,
    base: usize,

    re_enter: usize,
}

impl Default for R8VM {
    fn default() -> Self {
        R8VM {
            stats: Default::default(),
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
            stdout: Arc::new(Mutex::new(Box::new(io::stdout()))),
            labels: Default::default(),
            debug_mode: VmDebugOpts::default(),
            frame: Default::default(),
            srctbl: Default::default(),
            trace_counts: Default::default(),
            re_enter: 0,
            base: 0,
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
        $vm.mem.push(PV::UInt(0));
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
        func.args.check($nargs as usize).map_err(|e| e.op($func))?;

        let frame = $vm.frame;

        $vm.frame = $vm.mem.stack.len();
        $body
        $vm.mem.push(PV::UInt(0));
        $vm.mem.push(PV::UInt(0));
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

pub struct Reader(u32);

impl Sexper for Reader {
    fn tlsexpre(&mut self, vm: &mut R8VM, num: u32, dot: bool) -> Result<PV> {
        vm.mem.list_dot(num, dot);
        Ok(vm.mem.pop().unwrap())
    }

    fn sexpre(&mut self, vm: &mut R8VM, v: PV) -> Result<PV> {
        Ok(v)
    }

    fn sexp(&mut self, vm: &mut R8VM, v: PV, _is_tail: bool, _src: Source) -> Result<()> {
        vm.mem.push(v);
        self.0 += 1;
        Ok(())
    }

    fn tlatom(&mut self, vm: &mut R8VM, v: PV, _is_tail: bool, _src: Source) -> Result<()> {
        vm.mem.push(v);
        self.0 += 1;
        Ok(())
    }

    fn finalize(self, vm: &mut R8VM) -> Result<PV> {
        vm.mem.list(self.0);
        let v = vm.mem.pop().unwrap();
        vm.mem.untag_ast(v);
        Ok(v)
    }
}

pub struct ReadCompile {
    cc: R8Compiler,
    modfn_pos: Option<IP>,
}

impl ReadCompile {
    pub fn new(vm: &R8VM) -> Self {
        Self { cc: R8Compiler::new(vm), modfn_pos: None }
    }
}

impl Sexper for ReadCompile {
    fn tlsexpre(&mut self, vm: &mut R8VM, num: u32, dot: bool) -> Result<PV> {
        vm.expand_from_stack(num, dot)
    }

    fn sexpre(&mut self, vm: &mut R8VM, v: PV) -> Result<PV> {
        vm.macroexpand_pv(v, false)
    }

    fn sexp(&mut self, vm: &mut R8VM, v: PV, is_tail: bool, src: Source) -> Result<()> {
        self.cc.set_offsets(vm);

        // FIXME: This is SLOW and has to be REMOVED removed
        self.cc.update_globals(vm);

        let excv = Excavator::new(&vm.mem);
        let file = src.file.clone();
        let mut ast = excv.to_ast(v, src)?;
        vm.mem.clear_tags();
        let mut opto = Optomat::new();
        opto.visit(&mut ast)?;
        if is_tail {
            self.modfn_pos = Some(self.cc.compile_top_tail(ast, file)?);
        } else {
            self.cc.compile_top(ast)?;
        }
        self.cc.take(vm)?;

        Ok(())
    }

    fn tlatom(&mut self, vm: &mut R8VM, v: PV, is_tail: bool, src: Source) -> Result<()> {
        let excv = Excavator::new(&vm.mem);
        let file = src.file.clone();
        let ast = excv.to_ast(v, src)?;
        if is_tail {
            self.modfn_pos = Some(self.cc.compile_top_tail(ast, file)?);
        } else {
            self.cc.compile_top(ast)?;
        }
        self.cc.take(vm)?;
        Ok(())
    }

    fn finalize(self, vm: &mut R8VM) -> Result<PV> {
        if let Some(pos) = self.modfn_pos {
            Ok(call_with!(vm, pos, 0, {}))
        } else {
            Ok(PV::Nil)
        }
    }
}

pub struct PMemIter<'a, Op: Sized + Copy> {
    max: NonNull<Op>,
    it: NonNull<Op>,
    _ph: PhantomData<&'a Op>,
}

impl<'a, Op: Sized + Copy> Iterator for PMemIter<'a, Op> {
    type Item = &'a Op;

    fn next(&mut self) -> Option<Self::Item> {
        if self.it == self.max {
            None
        } else {
            Some(unsafe {
                let r = self.it;
                self.it = self.it.add(1);
                r.as_ref()
            })
        }
    }
}

pub struct PMemIterMut<'a, Op: Sized + Copy> {
    max: NonNull<Op>,
    it: NonNull<Op>,
    _ph: PhantomData<&'a Op>,
}

impl<'a, Op: Sized + Copy> Iterator for PMemIterMut<'a, Op> {
    type Item = &'a mut Op;

    fn next(&mut self) -> Option<Self::Item> {
        if self.it == self.max {
            None
        } else {
            Some(unsafe {
                let mut r = self.it;
                self.it = self.it.add(1);
                r.as_mut()
            })
        }
    }
}

impl<Op: Sized + Copy + Debug> fmt::Debug for PMem<Op> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[ ")?;
        for op in self.iter() {
            write!(f, "{op:?}; ")?;
        }
        write!(f, "]")
    }
}

impl<Op: Sized + Copy + PartialEq> PartialEq for PMem<Op> {
    fn eq(&self, other: &Self) -> bool {
        for (u, v) in self.iter().zip(other.iter()) {
            if u != v {
                return false
            }
        }
        true
    }
}

impl<Op: Sized + Copy + Eq> Eq for PMem<Op> {}

impl<Op: Sized + Copy> Default for PMem<Op> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
pub struct IPtr<Op: Sized + Copy>(u32, PhantomData<Op>);

pub type IP = IPtr<r8c::Op>;

impl<Op: Sized + Copy> Into<u32> for IPtr<Op> {
    fn into(self) -> u32 {
        self.0
    }
}

impl<Op: Sized + Copy> Eq for IPtr<Op> {}

impl<Op: Sized + Copy> PartialEq for IPtr<Op> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<Op: Sized + Copy> Ord for IPtr<Op> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<Op: Sized + Copy> PartialOrd for IPtr<Op> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<Op: Sized + Copy> Display for IPtr<Op> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IPtr({})", self.0)
    }
}

impl<Op: Sized + Copy> TryInto<usize> for IPtr<Op> {
    type Error = Infallible;
    fn try_into(self) -> std::result::Result<usize, Self::Error> {
        Ok(self.0 as usize)
    }
}

impl<Op: Sized + Copy> fmt::Debug for IPtr<Op> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IPtr({})", self.0)
    }
}

impl<Op: Sized + Copy> IPtr<Op> {
    pub fn new(base: NonNull<Op>, ip: NonNull<Op>) -> Self {
        assert!(ip >= base);
        IPtr(((ip.as_ptr() as usize - base.as_ptr() as usize) / size_of::<Op>()) as u32,
            PhantomData::default())
    }

    pub fn from_offset(offset: usize) -> Self {
        IPtr(offset.try_into().unwrap(), PhantomData::default())
    }

    pub fn from_offset_u32(offset: u32) -> Self {
        IPtr(offset, PhantomData::default())
    }

    pub unsafe fn to_ptr(&self, base: NonNull<Op>) -> NonNull<Op> {
        base.add(self.0 as usize)
    }

    pub fn prev(&self) -> Self {
        assert_ne!(self.0, 0);
        IPtr(self.0 - 1, self.1)
    }

    pub fn after(&self, a: u32) -> Self {
        IPtr(self.0 + a as u32, self.1)
    }

    pub fn add(&self, a: i32) -> Self {
        IPtr((self.0 as i32 + a) as u32, self.1)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl Into<PV> for IPtr<r8c::Op> {
    fn into(self) -> PV {
        PV::UInt(self.0 as usize)
    }
}

pub struct PMem<Op: Sized + Copy> {
    ops: NonNull<Op>,
    sz: usize,
    len: usize,
    ip: NonNull<Op>,
}

impl<Op: Sized + Copy> PMem<Op> {
    fn layout(&self) -> Layout {
        Layout::from_size_align(self.sz*size_of::<Op>(), align_of::<Op>()).unwrap()
    }

    pub fn new() -> Self {
        let sz = 4096;
        let layout = Layout::from_size_align(sz*size_of::<Op>(), align_of::<Op>())
            .unwrap();
        let ops = unsafe {
            let p = alloc(layout) as *mut Op;
            NonNull::new(p).expect("Allocation error")
        };
        Self {
            ops,
            sz,
            len: 0,
            ip: ops,
        }
    }

    pub fn advance(&mut self) -> Op {
        let op = self.op();
        self.ip = unsafe { self.ip.add(1) };
        op
    }

    pub fn op(&self) -> Op {
        unsafe { self.ip.read() }
    }

    pub fn ip(&self) -> IPtr<Op> {
        IPtr::new(self.ops, self.ip)
    }

    pub fn goto(&mut self, ip: IPtr<Op>) {
        unsafe {
            self.ip = ip.to_ptr(self.ops);
        }
    }

    pub fn jmp(&mut self, dip: i32) {
        unsafe {
            self.ip = self.ip.offset(dip as isize);
        }
    }

    pub fn push_op(&mut self, op: Op) {
        unsafe {
            self.fit(1);
            ptr::write(self.ops.add(self.len).as_ptr(), op);
            self.len += 1;
        }
    }

    pub fn ip_at_end(&self) -> IPtr<Op> {
        IPtr::from_offset(self.len())
    }

    pub fn ip_halt(&self) -> IPtr<Op> {
        IPtr::from_offset(0)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn shrink_to_fit(&self) {
        log::trace!("PMem::shrink_to_fit is a no-op");
    }

    pub unsafe fn get_unchecked(&self, idx: impl TryInto<usize>) -> &Op {
        let Ok(idx) = idx.try_into() else {
            panic!("Integer (somehow) doesn't fit into usize")
        };
        self.ops.add(idx).as_ref()
    }

    pub unsafe fn get_mut_unchecked(&mut self, idx: impl TryInto<usize>) -> &mut Op {
        let Ok(idx) = idx.try_into() else {
            panic!("Integer (somehow) doesn't fit into usize")
        };
        self.ops.add(idx).as_mut()
    }

    pub fn get(&self, idx: impl TryInto<usize>) -> Option<&Op> {
        let Ok(idx) = idx.try_into() else {
            panic!("Integer (somehow) doesn't fit into usize")
        };
        (idx < self.len).then(|| unsafe { self.get_unchecked(idx) })
    }

    pub fn get_mut(&mut self, idx: impl TryInto<usize>) -> Option<&mut Op> {
        let Ok(idx) = idx.try_into() else {
            panic!("Integer (somehow) doesn't fit into usize")
        };
        (idx < self.len).then(|| unsafe { self.get_mut_unchecked(idx) })
    }

    fn fit(&mut self, extra: usize) {
        if self.len + extra >= self.sz {
            let ip = self.ip();
            let nsz = cmp::max(self.sz * 2, self.len + extra);
            let p = unsafe {
                realloc(self.ops.as_ptr() as *mut u8, self.layout(), nsz*size_of::<Op>()) as *mut Op
            };
            self.ops = NonNull::new(p).expect("Allocation error");
            self.sz = nsz;
            self.goto(ip);
        }
    }

    pub fn append(&mut self, it: &mut Vec<Op>) -> Result<()> {
        unsafe {
            self.fit(it.len());
            ptr::copy_nonoverlapping(
                it.as_ptr(), self.ops.add(self.len).as_ptr(), it.len()
            );
            self.len += it.len();
            it.clear();
        }
        Ok(())
    }

    pub fn iter<'a>(&'a self) -> PMemIter<'a, Op> {
        unsafe {
            PMemIter { max: self.ops.add(self.len), it: self.ops, _ph: Default::default() }
        }
    }

    pub fn iter_mut<'a>(&'a self) -> PMemIterMut<'a, Op> {
        unsafe {
            PMemIterMut { max: self.ops.add(self.len), it: self.ops, _ph: Default::default() }
        }
    }

    pub fn as_slice(&self) -> &[Op] {
        unsafe {
            std::slice::from_raw_parts(self.ops.as_ptr(), self.len)
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [Op] {
        unsafe {
            std::slice::from_raw_parts_mut(self.ops.as_ptr(), self.len)
        }
    }
}

impl<Op: Sized + Copy> ops::Deref for PMem<Op> {
    type Target = [Op];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<Op: Sized + Copy> ops::DerefMut for PMem<Op> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<Op: Sized + Copy, Idx> Index<Idx> for PMem<Op>
where Idx: TryInto<usize>
{
    type Output = Op;
    fn index(&self, index: Idx) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

impl<Op: Sized + Copy, Idx> IndexMut<Idx> for PMem<Op>
where Idx: TryInto<usize>
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
        self.get_mut(index).expect("index out of bounds")
    }
}

impl<Op: Sized + Copy> Clone for PMem<Op> {
    fn clone(&self) -> Self {
        Self {
            ops: unsafe {
                let p = NonNull::new(alloc(self.layout()) as *mut Op)
                    .expect("Allocation error");
                ptr::copy_nonoverlapping(self.ops.as_ptr(), p.as_ptr(), self.len);
                p
            }, ..(*self)
        }
    }
}

impl<Op: Sized + Copy> Drop for PMem<Op> {
    fn drop(&mut self) {
        unsafe {
            dealloc(self.ops.as_ptr() as *mut u8, self.layout());
        }
    }
}

pub type PMemT = PMem<r8c::Op>;
// pub type PMemT = Vec<r8c::Op>;

impl R8VM {
    pub fn no_std() -> R8VM {
        // let mut pmem = Vec::with_capacity(1024 * 1024);
        let mut pmem: PMemT = Default::default();
        pmem.push_op(r8c::Op::HCF());
        let mut vm = R8VM {
            pmem, ..Default::default()
        };

        for i in 0..=MAX_CLZCALL_ARGS {
            let pos = vm.pmem.ip_at_end();
            vm.pmem.push_op(r8c::Op::ZCALL(i));
            vm.pmem.push_op(r8c::Op::RET());
            let sym = vm.mem.symdb.put(format!("<ζ>-λ/{i}")).id();
            vm.funcs.insert(sym, Func {
                pos,
                sz: 2,
                args: ArgSpec::normal(0)
            });
        }

        vm.funcs.insert(Builtin::HaltFunc.sym_id(), Func {
            pos: vm.pmem.ip_halt(),
            sz: 1,
            args: ArgSpec::none()
        });

        macro_rules! addfn {
            ($fn:ident) => {
                let sym = vm.mem.symdb.put_ref(sysfns::$fn.name()).id();
                vm.set(sym, (sysfns::$fn).into_subr()).unwrap();
            };

            ($name:expr, $fn:ident) => {
                let sym = vm.mem.symdb.put_ref($name).id();
                vm.set(sym, (sysfns::$fn).into_subr()).unwrap();
            };
        }

        // IO
        addfn!(println);
        addfn!(print);
        addfn!(slurp);

        // Modules
        #[cfg(any(not(target_arch = "wasm32"), target_os = "wasi"))] {
            addfn!(load);
            addfn!(require);
            addfn!(instant);
            addfn!(read_from);
            addfn!(read_compile_from);
        }

        // Meta
        addfn!(eval);
        addfn!(read);
        addfn!(macroexpand);
        addfn!(clone);
        addfn!(copy);
        addfn!(intern);
        addfn!(gc);
        addfn!("sys/freeze", freeze);
        addfn!(read_compile);
        addfn!(type_of);
        addfn!(sym_id);
        addfn!("sys/set-macro", set_macro);
        addfn!("sys/set-macro-character", set_macro_character);
        addfn!(is_void);
        addfn!(is_mut_locked);

        // Debug
        #[cfg(feature = "extra")] {
            addfn!(dump_all_fns);
            addfn!(dump_code_to);
            addfn!(dump_code);
            addfn!(dump_macro_tbl);
            addfn!(dump_sym_tbl);
            addfn!(dump_env_tbl);
            addfn!(dump_fn_tbl);
            addfn!(dump_gc_stats);
            addfn!(dump_stack);
            addfn!(debug_mode);
            addfn!(disassemble);
            addfn!(dump_mem);
        }

        // Meta
        addfn!(globals);
        addfn!(functions);

        // Tables
        addfn!(make_table);
        addfn!(del);

        // Control-Flow
        addfn!(panic);
        addfn!(error);
        addfn!(exit);

        // Arithmetic
        addfn!("%", modulo);
        addfn!(sum);
        addfn!(asum);
        addfn!(product);
        addfn!(aproduct);
        addfn!(pow);
        addfn!(vec2);
        addfn!(vec3);
        addfn!(vec4);
        addfn!(mat2_rot);
        addfn!(mat3_rot_x);
        addfn!(mat3_rot_y);
        addfn!(mat3_rot_z);
        addfn!(mat4_rot_x);
        addfn!(mat4_rot_y);
        addfn!(mat4_rot_z);
        addfn!(mat);
        addfn!(scale);
        addfn!(translate);
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
        addfn!(atan2);
        addfn!(atanh);
        addfn!(round);
        addfn!(int);
        addfn!(ceil);
        addfn!(floor);
        addfn!(ln);
        addfn!(tan);
        addfn!(tanh);
        addfn!(sysrand);

        // Strings
        addfn!(string);
        addfn!(repr);
        addfn!(dbg_repr);
        addfn!(concat);
        addfn!(join);

        // Iter
        addfn!(iter);

        // Utils
        addfn!(sort_inplace);
        addfn!(split_mut);
        addfn!(reverse);
        addfn!(reverse_inplace);

        // TODO
        // addfn!(list);
        // addfn!(vec);
        // addfn!(append);
        // addfn!("=", eq);
        // addfn!("eq?", eqp);
        // addfn!(">", gt);
        // addfn!(">=", gte);
        // addfn!("<", lt);
        // addfn!("<=", lte);

        let src = Some(Cow::Borrowed("<ζ>::boot-stage0"));
        vm.read_compile(include_str!("../lisp/boot-stage0.lisp"),
                        src.clone()).unwrap();

        vm
    }

    pub fn get_fn_names(&self) -> Vec<PV> {
        let mut names = vec![];
        for (name, idx) in self.globals.iter() {
            let env = self.mem.env[*idx];
            let t = env.bt_type_of();
            if t == Builtin::Lambda || t == Builtin::Subr {
                names.push(PV::Sym(*name));
            }
        }
        for (name, _) in self.funcs.iter() {
            if name.as_ref().starts_with("<ξ>-") ||
                name.as_ref().starts_with("<λ>-") ||
                name.as_ref().starts_with("<ζ>-") ||
                name.as_ref().starts_with("<δ>-") ||
                name.as_ref().starts_with("<σ>-") {
                continue;
            }
            names.push(PV::Sym(*name));
        }
        names
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

    pub fn vm_id(&self) -> VmId {
        self.mem.vm_id()
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
            let fn_pos = self.pmem.ip_at_end();
            self.pmem.push_op(r8c::Op::GET(obj_idx as u16));
            self.pmem.push_op(r8c::Op::INS(name_idx as u32));
            assert!(!spec.is_special(), "No special function signatures allowed for methods");
            for i in 0..spec.nargs {
                self.pmem.push_op(r8c::Op::MOV(i));
            }
            self.pmem.push_op(r8c::Op::ZCALL(spec.nargs + 1));
            self.pmem.push_op(r8c::Op::RET());
            let posi: u32 = fn_pos.into();
            let sz = self.pmem.len() as u32 - posi;
            // TODO: Add arg names, they have to be generated in the methods proc-macro
            self.defun(fn_name, *spec, vec![], fn_pos, sz);
        }
    }

    pub unsafe fn set_resource<T: Userdata>(&mut self, rf: &mut T) {
        let idx = self.resource_idx::<T>();
        if let PV::Ref(p) = self.mem.env[idx as usize] {
            if let Some(obj) = cast_mut::<Object>(p) {
                (*obj).put_ref(rf);
                self.mem.push_borrow(p);
                return;
            }
        }
        let obj = rf.into_pv(&mut self.mem).unwrap();
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

    pub unsafe fn call_method(&mut self, ip: IP, obj: *mut Object, args: &[PV]) -> Result<PV> {
        let kw = args.first()
                     .ok_or_else(|| error!(NoMethodGiven, vt: (*obj).vt))
                     .and_then(|f| f.sym())?;
        let key = ((*obj).type_id , kw);
        match self.obj_methods.get(&key) {
            Some(f) => (f)((*obj).mem, self, &args[1..]).map_err(|e| {
                e.insert_traceframe(self.get_source(ip.prev()),
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
        #[cfg(feature = "gc-assertions")]
        log::warn!("Running with GC assertions enabled, this will be VERY SLOW!");

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

    pub fn set_debug_mode(&mut self, debug_mode: VmDebugOpts) {
        self.debug_mode = debug_mode;
    }

    pub fn catch(&mut self, dip: IP, sym: Option<SymID>) {
        let frame = self.frame - self.base;
        let top = self.mem.stack.len() - self.base;
        self.catch.push(Guard {
            top, sym: sym.map(|s| s.as_int() as usize), frame, dip,
        })
    }

    pub fn catch_pop(&mut self) {
        self.catch.pop();
    }

    pub fn catch_clear(&mut self) {
        self.catch.clear()
    }

    pub fn fixup_frame(&self, frame: usize) -> usize {
        self.base + frame
    }

    pub fn inv_fixup_frame(&self, frame: usize) -> usize {
        (frame as isize - self.base as isize).try_into().expect("underflow")
    }

    pub fn op_unwind(&mut self) -> Result<IP> {
        let tag_sym = self.mem.pop().and_then(|s| s.sym()).map_err(|e| e.bop(Builtin::Throw))?;
        let tag = tag_sym.as_int() as usize;
        let val = self.mem.pop()?;
        let (catchp, frame, dip) = loop {
            let Some(Guard { dip, sym, top, frame }) = self.catch.pop() else {
                bail!(Throw { tag: tag_sym.into(),
                              obj: NonRef::new(val)? })
            };
            match sym {
                Some(stag) if tag == stag => break (top, frame, dip),
                None => break (top, frame, dip),
                _ => ()
            }
        };
        self.frame = self.base + frame;
        self.mem.stack.truncate(self.base + catchp);
        self.mem.stack.push(val);
        Ok(dip)
    }

    pub fn get_func(&self, name: SymID) -> Option<&Func> {
        self.funcs.get(&name)
    }

    /// Find a library by name, returns the path to the library as a LibrarySrc,
    /// which will be New(path) if the file is modified or has not been loaded,
    /// or Exists(path) if the file is already loaded and has not been modified.
    pub fn find_lib_src(&mut self, lib: SymID) -> Result<LibrarySrc<'_>> {
        let it = self.var(Builtin::SysLoadPath.sym_id())?
                     .make_iter()
                     .map_err(|e| e.bop(Builtin::SysLoad))?;
        for (i, p) in it.enumerate() {
            let mut path = PathBuf::from(with_ref!(p, String(s) => {Ok(&(**s)[..])})
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

    pub fn load_eval_path(&mut self, path: impl AsRef<Path>) -> Result<PV> {
        let src = fs::read_to_string(path.as_ref())?;
        let src_name = Some(Cow::Owned(path.as_ref().to_string_lossy().into_owned()));
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

    /// Reads LISP code into an AST from file.
    pub fn read_from(&mut self, path: impl AsRef<Path>) -> Result<PV> {
        let sexpr = fs::read_to_string(path.as_ref())?;
        let name = path.as_ref().file_stem().map(|p| {
            p.to_string_lossy().into_owned()
        }).map(Cow::from);
        self.read(&format!("'({sexpr})"), name)
    }

    pub fn read_compile_from(&mut self, path: impl AsRef<Path>) -> Result<PV> {
        let sexpr = fs::read_to_string(path.as_ref())?;
        let name = path.as_ref().file_stem().map(|p| {
            p.to_string_lossy().into_owned()
        }).map(Cow::from);
        self.read_compile(&sexpr, name)
    }

    pub fn read(&mut self, sexpr: &str, file: SourceFileName) -> Result<PV> {
        let tok_tree = self.tok_tree.clone();
        let toker = tokit::Toker::new(sexpr, &tok_tree);
        let rc = Reader(0);
        let sexpert = Sexpert::new(rc, toker, self.reader_macros.clone(), file);
        sexpert.read(self)
    }

    pub fn read_compile(&mut self, sexpr: &str, file: SourceFileName) -> Result<PV> {
        let tok_tree = self.tok_tree.clone();
        let toker = tokit::Toker::new(sexpr, &tok_tree);
        let rc = ReadCompile::new(self);
        let sexpert = Sexpert::new(rc, toker, self.reader_macros.clone(), file);
        sexpert.read(self)
    }

    fn expand_from_stack(&mut self, n: u32, dot: bool) -> Result<PV> {
        let op = self.mem.from_top(n as usize);
        let v = if let Some(m) = op.sym().ok().and_then(|op| self.macros.get(&op)).copied() {
            if dot {
                return Err(error!(UnexpectedDottedList,).bop(Builtin::Apply))
            }
            let func = self.funcs.get(&m).ok_or("No such function")?;
            let chk = func.args.check((n - 1) as usize).map_err(|e| e.op(m));
            if let Err(e) = chk {
                self.mem.popn(n as usize);
                return Err(e);
            }
            let frame = self.frame;
            self.frame = self.mem.stack.len() - (n as usize) + 1;
            self.mem.push(PV::UInt(0));
            self.mem.push(PV::UInt(0));
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
                v.set_inner(nv)?;
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
                if let Err(e) = func.args.check(nargs as usize).map_err(|e| e.op(m)) {
                    // Pop arguments off stack again in case of error, and
                    // restore call-frame
                    self.mem.popn(nargs as usize);
                    self.frame = frame;
                    return Err(e);
                }

                // Push previous call-frame and run macro
                self.mem.push(PV::UInt(0));
                self.mem.push(PV::UInt(0));
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

    fn get_source(&self, idx: IPtr<r8c::Op>) -> Source {
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

    pub fn defvar(&mut self, name: SymID, idx: usize, pos: IP) -> Result<()> {
        let res = call_with!(self, pos, 0, {});
        self.mem.set_env(idx, res);
        self.globals.insert(name, idx);
        Ok(())
    }

    pub fn defun(&mut self,
                 name: SymID,
                 args: ArgSpec,
                 arg_names: Vec<SymID>,
                 pos: IP,
                 sz: u32)
    {
        match self.funcs.entry(name) {
            Entry::Occupied(mut e) => {
                let ppos = e.get().pos;
                use r8c::Op::*;
                for op in self.pmem.iter_mut() {
                    *op = match *op {
                        CALL(p, nargs) if p == ppos.into() =>
                            CALL(pos.into(), nargs),
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
    pub fn unwind_traceback(&mut self, mut ip: IP, err: Error) -> Traceback {
        let mut pos_to_fn: Vec<(IP, SymID)> = Vec::new();
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

        while !ip.is_zero() {
            let mut name = get_name(ip);
            let func = self.funcs
                           .get(&name)
                           .expect("Unable to find function by binary search");

            let (nenv, nargs) = if func.pos.after(func.sz) < ip {
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
            if frame+1 >= self.mem.stack.len() {
                log::warn!("Incomplete stack trace!");
                break;
            }
            ip = match self.mem.stack[frame] {
                PV::UInt(x) => IPtr::from_offset(x),
                _ => {
                    log::warn!("Incomplete stack trace!");
                    break;
                }
            };
            self.frame = match self.mem.stack[frame+1] {
                PV::UInt(x) => self.fixup_frame(x),
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
    fn traceframe(&self, ip: IP) -> SymID {
        let mut pos_to_fn: Vec<(IP, SymID)> = Vec::new();
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
    fn count_trace(&mut self, ip: IP) {
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

    unsafe fn run_from_unwind(&mut self, ip: IP, pframe: usize, internal: bool)
                              -> std::result::Result<IP, Traceback>
    {
        let cth = mem::replace(&mut self.catch, Default::default());
        let base = self.base;
        self.base = self.frame;
        self.re_enter += 1;
        let res = match self.run_from(ip) {
            Ok(ip) => Ok(ip),
            Err((ip, e)) => {
                Err(self.unwind_traceback(ip, e))
            },
        };
        self.base = base;
        self.re_enter -= 1;
        if !internal {
            self.mem.pop_borrows();
        }
        self.catch = cth;
        self.frame = pframe;
        res
    }

    fn op_yeet(&mut self) -> Result<IP> {
        let cc = self.mem.pop()?;
        let tag = self.mem.pop()?;
        let val = self.mem.pop()?;
        let _dip = with_ref!(cc, Continuation(cont) => {
            Ok(self.warp(&*cont, PV::Nil))
        })?;
        self.mem.push(val);
        self.mem.push(tag);
        self.op_unwind()
    }

    fn warp(&mut self, cont: &Continuation, val: PV) -> IP {
        self.mem.stack.truncate(self.base);
        self.mem.stack.extend((*cont).stack.iter());
        self.catch.clear();
        self.catch.extend((*cont).catch.iter());
        self.mem.stack.push(val);
        self.frame = self.fixup_frame((*cont).frame);
        cont.dip
    }

    #[inline]
    fn op_clzcall(&mut self,
                  ip: IP,
                  nargs: usize) -> Result<IP> {
        let idx = self.mem.stack.len() - nargs - 1;
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
                    - nargs
                    - has_env as usize;
                Ok((*lambda).pos)
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
                let args: Vec<_> = self.mem.stack[top - nargs..].to_vec();

                let name = OpName::OpStr((*subr).name());
                let res = (*subr).call(self, &args[..]).map_err(|e| {
                    e.insert_traceframe(self.get_source(ip.prev()), name, &[])
                });
                invalid!(args, subr); // (*subr).call
                self.mem.stack.drain(idx..).for_each(drop); // drain gang
                self.mem.push(res?);
                Ok(ip)
            }
            NkT::Continuation => unsafe {
                let cont = fastcast::<Continuation>(p);
                ArgSpec::normal(1).check(nargs).map_err(|e| e.bop(Builtin::Continuation))?;
                let pv = self.mem.pop().unwrap();
                let dip = self.warp(&*cont, pv);
                Ok(dip)
            }
            NkT::Object => unsafe {
                let s = fastcast_mut::<Object>(p);
                let top = self.mem.stack.len();
                let args: Vec<_> = self.mem.stack[top - nargs..].to_vec();
                let res = self.call_method(ip, s, &args[..]);
                self.mem.stack.drain(idx..).for_each(drop); // drain gang
                self.mem.push(res?);
                Ok(ip)
            }
            _ => err()
        }
    }

    #[inline(never)]
    fn vcall(&mut self, ip: IPtr<r8c::Op>, idx: u32, nargs: usize) -> Result<IPtr<r8c::Op>> {
        let sym = self.mem.env[idx as usize].sym().unwrap();
        match self.funcs.get(&sym) {
            Some(func) => {
                func.args.check(nargs).map_err(|e| e.op(sym))?;
                let pos = func.pos;
                // FIXME: This does not pass in miri because of aliasing
                // (*ip.sub(1)) = CALL(pos as u32, nargs);
                self.call_pre(ip);
                self.frame = self.mem.stack.len() - 2 - (nargs as usize);
                Ok(pos)
            },
            None => if let Some(idx) = self.get_env_global(sym) {
                let var = self.mem.get_env(idx);
                let sidx = self.mem.stack.len() - nargs as usize;
                // FIXME: This can be made less clunky by modifying
                // op_clzcall so that it takes the callable as a parameter.
                self.mem.stack.insert(sidx, var);
                self.op_clzcall(ip, nargs)
            } else {
                return Err(ErrorKind::UndefinedFunction {
                    name: sym.into()
                }.into())
            }
        }
    }

    #[inline(never)]
    unsafe fn apl(&mut self, ip: IP) -> Result<IP> {
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
        self.op_clzcall(ip, nargs)
    }

    /**
     * Start running code from a point in program memory.
     *
     * NOTE: If the code isn't well-formed, i.e produces out-of-bounds jumps,
     * then you've yee'd your last haw.
     */
    unsafe fn run_from(&mut self, ip: IP) -> std::result::Result<IP, (IP, Error)> {
        if self.debug_mode.show_frames {
            eprintln!("[run_from {ip}]");
            self.dump_stack().unwrap();
        }
        let mut regs: Regs<2> = Regs::new();
        self.pmem.goto(ip);
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
        let mut orig = None;
        if self.debug_mode.show_frames {
            let sym = self.traceframe(ip);
            orig = Some(sym);
            eprintln!("{}:", sym);
        }
        macro_rules! barrier {
            ($v:expr) => {{
                let q = $v;
                if let PV::Ref(p) = q {
                    unsafe {
                        if (*p).color() == Color::White {
                            (*p).set_color(Color::Gray);
                            self.mem.gray.push(p);
                        }
                    }
                }
                q
            }};
        }
        let mut run = || loop {
            let op = self.pmem.op();
            self.pmem.advance();

            if self.debug_mode.show_frames {
                match op {
                    VCALL(f, _) => eprintln!("{}:", f),
                    CALL(ip, _) => {
                        let sym = self.traceframe(IPtr::from_offset_u32(ip));
                        eprintln!("{}:", sym);
                    }
                    _ => ()
                }
            }

            if self.debug_mode.show_opcodes {
                eprintln!("  {} {}", ip, op);
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
                    let it = self.mem.stack[self.frame + var as usize];
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
                    for item in vec.iter() {
                        barrier!(*item);
                    }
                    let ptr = self.mem.put_pv(vec);
                    self.mem.push(ptr);
                }
                VPUSH() => {
                    let vec = self.mem.pop()?;
                    let elem = self.mem.pop()?;
                    with_ref_mut!(vec, Vector(v) => {
                        (*v).push(barrier!(elem));
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
                                     Builtin::Vec3,
                                     Builtin::Table],
                        got: vec.bt_type_of(),
                    });
                    #[cfg(feature = "math")]
                    let ierr = |x: PV| Err(error!(TypeError,
                                                  expect: Builtin::Integer,
                                                  got: x.bt_type_of()).bop(Builtin::Get).argn(2));
                    let elem = match (idx, vec) {
                        (idx, PV::Ref(p)) => match (idx, atom_kind(p)) {
                            (PV::Int(idx), NkT::Vector) => if idx < 0 {
                                bail!(IndexError { idx })
                            } else {
                                (**fastcast::<Vec<PV>>(p)).get(idx as usize)
                                                          .ok_or(error!(IndexError, idx))
                                                          .copied()
                            }
                            (x, NkT::Vector) => return ierr(x).map(|_| ())
                                                              .map_err(|e| {
                                                                  e.object(Builtin::Vector)
                                                                   .subject("index")
                                                              }),
                            (PV::Ref(_), NkT::Table) => err!(KeyReference, key: idx.to_string()),
                            (idx, NkT::Table) =>
                                Ok((*fastcast::<HMap<PV, PV>>(p)).get(&idx).copied().unwrap_or_default()),
                            _ => Err(err())
                        }
                        #[cfg(feature = "math")] (PV::Int(0), PV::Vec2(glam::Vec2 { x, .. })) => Ok(PV::Real(x)),
                        #[cfg(feature = "math")] (PV::Int(1), PV::Vec2(glam::Vec2 { y, .. })) => Ok(PV::Real(y)),
                        #[cfg(feature = "math")] (PV::Int(x), PV::Vec2(_)) => err!(IndexError, idx: x),
                        #[cfg(feature = "math")] (x, PV::Vec2(_)) =>
                            ierr(x).map_err(|e| e.object(Builtin::Vec2).subject("index")),
                        #[cfg(feature = "math")] (PV::Int(0), PV::Vec3(glam::Vec3 { x, .. })) => Ok(PV::Real(x)),
                        #[cfg(feature = "math")] (PV::Int(1), PV::Vec3(glam::Vec3 { y, .. })) => Ok(PV::Real(y)),
                        #[cfg(feature = "math")] (PV::Int(2), PV::Vec3(glam::Vec3 { z, .. })) => Ok(PV::Real(z)),
                        #[cfg(feature = "math")] (PV::Int(x), PV::Vec3(_)) => err!(IndexError, idx: x),
                        #[cfg(feature = "math")] (x, PV::Vec3(_)) =>
                            ierr(x).map_err(|e| e.object(Builtin::Vec3).subject("index")),
                        _ => Err(err())
                    }.map_err(|e| e.bop(Builtin::Get))?;
                    self.mem.push(elem);
                }
                VSET() => {
                    // (set (get <vec> <idx>) <val>)
                    let len = self.mem.stack.len();
                    let args = &mut self.mem.stack[len - 3..];
                    with_ref_mut!(args[1], Vector(v) => {
                        let idx = args[2].int().map_err(|e| {
                            e.bop(Builtin::Set).argn(2)
                             .object(Builtin::Vector).subject("index")
                        })?;
                        if idx < 0 || idx as usize >= (*v).len() {
                            err!(IndexError, idx)
                        } else {
                            *(**v).get_unchecked_mut(idx as usize) = barrier!(args[0]);
                            Ok(())
                        }
                    }, Table(t) => {
                        if args[2].is_ref() {
                            err!(KeyReference, key: args[2].to_string())
                        } else {
                            (*t).insert(args[2], barrier!(args[0]));
                            Ok(())
                        }
                    }).map_err(|e| e.bop(Builtin::Set))?;
                    self.mem.stack.truncate(len - 3);
                }
                LEN() => {
                    let li = self.mem.pop()?;
                    self.mem.push(li.len()?);
                }

                // Value creation
                NIL() => self.mem.push(PV::Nil),
                INS(idx) => {
                    let pv = self.mem.get_env(idx as usize).deep_clone(&mut self.mem)?;
                    self.mem.push(pv);
                },
                BOOL(i) => self.mem.push(PV::Bool(i != 0)),
                ZAV(nargs, nenv) => {
                    let frame = self.frame;
                    let start_idx = frame + nargs as usize;
                    let end_idx = start_idx + nenv as usize;
                    let lambda = self.mem.stack[frame];
                    let new_env = &self.mem.stack[start_idx..end_idx];
                    // Save environment
                    with_ref_mut!(lambda, Lambda(lambda) => {
                        for (dst, var) in (*lambda).locals.iter_mut().zip(new_env.iter()) {
                            *dst = barrier!(*var);
                        }
                        Ok(())
                    })?;
                }
                ARGS(_nargs, _nopt, _env, _rest) => {}
                CLZ(pos, nenv) => {
                    let ipd = self.pmem.ip();
                    let ARGS(nargs, nopt, env, rest) = *self.pmem.get_unchecked(ipd.prev().prev()) else {
                        panic!("CLZR without ARGSPEC");
                    };
                    let spec = ArgSpec { nargs, nopt, env, rest: rest == 1 };
                    let to = self.mem.stack.len();
                    let from = to - nenv as usize;
                    let locals = self.mem.stack.drain(from..to).collect::<Vec<_>>();
                    for x in locals.iter() {
                        barrier!(*x);
                    }
                    self.mem.push_new(nkgc::Lambda { pos: IPtr::from_offset_u32(pos),
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
                JMP(d) => self.pmem.jmp(d - 1),
                JT(d) => if bool::from(self.mem.pop()?) {
                    self.pmem.jmp(d - 1);
                }
                JN(d) => if !bool::from(self.mem.pop()?) {
                    self.pmem.jmp(d - 1);
                }
                JZ(d) => if self.mem.stack.pop() == Some(PV::Int(0)) {
                    self.pmem.jmp(d - 1);
                }
                JNZ(d) => if self.mem.stack.pop() != Some(PV::Int(0)) {
                    self.pmem.jmp(d - 1);
                }
                JV(mul, max) => {
                    let n = self.mem.pop()?.force_int() as i32;
                    let d = cmp::min((mul as i32) * n, max as i32);
                    self.pmem.jmp(d);
                }
                VCALL(idx, nargs) => {
                    let ipd = self.vcall(self.pmem.ip(), idx, nargs.into())?;
                    self.pmem.goto(ipd);
                },
                CALL(pos, nargs) => {
                    self.call_pre(self.pmem.ip());
                    self.frame = self.mem.stack.len() - 2 - (nargs as usize);
                    self.pmem.goto(IPtr::from_offset_u32(pos));
                }
                RET() => {
                    if self.debug_mode.show_stack_on_ret {
                        self.dump_stack().unwrap();
                    }
                    let rv = self.mem.pop()?;
                    let old_frame = self.frame;
                    let frame_pv = self.mem.pop()?;
                    let dip_pv = self.mem.pop()?;
                    let (PV::UInt(frame), PV::UInt(dip)) = (frame_pv, dip_pv) else {
                        self.mem.push(rv);
                        self.mem.push(dip_pv);
                        self.mem.push(frame_pv);
                        self.dump_stack().unwrap();
                        panic!("Invalid frame, expected two unsigned-integers")
                    };
                    self.frame = self.fixup_frame(frame);
                    self.pmem.goto(IPtr::from_offset(dip));
                    // yeet the stack frame
                    self.mem.stack.truncate(old_frame);
                    self.mem.push(rv);
                    assert!(self.frame <= self.mem.stack.len());
                }
                ZCALL(nargs) => {
                    let ipd = self.op_clzcall(self.pmem.ip(), nargs as usize)?;
                    self.pmem.goto(ipd);
                },
                APL() => {
                    let ipd = self.apl(self.pmem.ip())?;
                    self.pmem.goto(ipd);
                },
                CCONT(dip) => {
                    let dip = self.pmem.ip().add(dip);
                    let mut stack = (&self.mem.stack[self.base..]).iter()
                                                                  .copied()
                                                                  .collect::<Vec<PV>>();
                    stack.pop();
                    let cnt = Continuation {
                        stack,
                        frame: self.inv_fixup_frame(self.frame),
                        dip,
                        catch: self.catch.clone(),
                    };
                    for v in cnt.stack.iter().copied() {
                        barrier!(v);
                    }
                    let cnt_pv = self.mem.put_pv(cnt);
                    self.mem.push(cnt_pv);
                    let dip = self.op_clzcall(self.pmem.ip(), 1)?;
                    self.pmem.goto(dip);
                }
                CTHPOP() => self.catch_pop(),
                CTH(dip) => {
                    let dip = self.pmem.ip().add(dip - 1);
                    let tag = self.mem.pop()
                                      .and_then(|pv| pv.sym())
                                      .map_err(|e| e.bop(Builtin::Catch)
                                               .argn(1)
                                               .arg_name(Builtin::Tag))?;
                    self.catch(dip, Some(tag));
                }
                UWND() => {
                    let dip = self.op_unwind()?;
                    self.pmem.goto(dip);
                }
                YEET() => {
                    let dip = self.op_yeet()?;
                    self.pmem.goto(dip);
                }

                // Stack manipulation
                MOV(var) => {
                    let offset = (self.frame as isize) + (var as isize);
                    self.mem
                        .push(*self.mem.stack.as_ptr().offset(offset))
                }
                STR(var) => {
                    let offset = (self.frame as isize) + (var as isize);
                    *(self.mem.stack.as_mut_ptr().offset(offset)) = barrier!(self.mem.pop()?)
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
                    let val = barrier!(self.mem.pop()?);
                    self.mem.set_env(var as usize, val);
                }

                MXP() => unimplemented!(),

                PRT() => unimplemented!(),

                EVL() => {
                    let dip = self.pmem.ip();
                    let v = self.mem.pop()?;
                    let res = self.eval_pv(v);
                    self.pmem.goto(dip);
                    match res {
                        Ok(x) => self.mem.push(x),
                        Err(e) => {
                            let (tag, v) = e.as_throw(self)?;
                            self.mem.push(v);
                            self.mem.push(tag);
                            let dip = self.op_unwind()?;
                            self.pmem.goto(dip);
                        },
                    }
                }

                HCF() => {
                    if self.debug_mode.show_frames {
                        eprintln!("hcf from {:?}", orig);
                    }
                    return Ok(())
                },
            }
            self.stats.instructions += 1;

            #[cfg(feature = "gc-assertions")]
            if self.debug_mode.assert_gc_invariants {
                self.mem.nuke.check_types_linear();

                if let Err((a, b)) = self.mem.assert_invariants() {
                    panic!("after {op}: Black object {a} points to white {b}");
                }
            }

            self.mem.collect();

            #[cfg(feature = "gc-assertions")]
            if self.debug_mode.assert_gc_invariants {
                self.mem.nuke.check_types_linear();

                if let Err((a, b)) = self.mem.assert_invariants() {
                    panic!("after collection: Black object {a} points to white {b}");
                }
            }
        };

        let res = run();
        if self.debug_mode.show_frames {
            eprintln!("[finished run_from {ip} with {res:?}]");
        }
        if self.debug_mode.show_stack_on_ret {
            self.dump_stack().unwrap();
        }

        let dip = self.pmem.ip();
        match res {
            Ok(_) => Ok(dip),
            Err(e) => {
                let er: Error = e;
                Err((dip, er.src(self.get_source(dip))))
            }
        }
    }

    pub fn log_stats(&self) {
        log::debug!("ran no. instructions: {}", self.stats.instructions);
        log::debug!("{:?}", self.mem.stats());
    }

    pub fn dump_stack(&mut self) -> Result<()> {
        const MAX_REPR_LEN: usize = 64;
        let mut stdout = self.stdout.lock().unwrap();
        writeln!(stdout, "stack:")?;
        if self.mem.stack.is_empty() {
            writeln!(stdout, "    (empty)")?;
        }
        for (idx, val) in self.mem.stack.iter().enumerate().rev() {
            let (idx, frame) = (idx as i64, self.frame as i64);
            write!(stdout, "{}", if idx == frame { " -> " } else { "    " })?;
            let repr = val.lisp_to_string();
            let repr = if repr.len() > MAX_REPR_LEN {
                repr.chars().take(MAX_REPR_LEN).chain("…".chars()).collect::<String>()
            } else {
                repr
            };
            writeln!(stdout, "{}: {}", idx - frame, repr)?;
        }
        Ok(())
    }

    #[inline]
    fn ret_to(&self, dip: usize) -> *const r8c::Op {
        &self.pmem[dip] as *const r8c::Op
    }

    #[inline]
    fn ip_delta(&self, ip: *const r8c::Op) -> usize {
        (ip as usize - self.ret_to(0) as usize) / mem::size_of::<r8c::Op>()
    }

    #[inline]
    fn call_pre(&mut self, dip: IPtr<r8c::Op>) {
        self.mem.push(dip.into());
        self.mem.push(PV::UInt(self.inv_fixup_frame(self.frame)));
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
        self.mem.push(PV::UInt(0));
        self.mem.push(f);
        let pos = IPtr::from_offset(clzcall_pad_dip(args.nargs().try_into()?));
        args.pusharg(&mut self.mem)?;
        unsafe {
            self.run_from_unwind(pos, frame, false)?;
        }
        self.frame = frame;
        self.mem.pop()
    }

    pub fn apply_spv(&mut self, f: SPV, args: impl AsArgs) -> Result<PV> {
        let frame = self.frame;
        self.frame = self.mem.stack.len();
        self.mem.push(PV::UInt(0));
        self.mem.push(PV::UInt(0));
        self.mem.push(f.pv(&self.mem));
        let pos = IPtr::from_offset(clzcall_pad_dip(args.inner_nargs().try_into()?));
        args.inner_pusharg(&mut self.mem)?;
        unsafe {
            self.run_from_unwind(pos, frame, false)?;
        }
        self.frame = frame;
        self.mem.pop()
    }

    pub fn eval_pv(&mut self, ast: PV) -> Result<PV> {
        self.macroexpand_pv(ast, false).and_then(|ast| {
            let excv = Excavator::new(&self.mem);
            let mut ast = excv.to_ast(ast, Source::none())?;
            let mut opto = Optomat::new();
            opto.visit(&mut ast)?;
            let mut cc = R8Compiler::new(self);
            let modfn_pos = cc.compile_top_tail(ast, None)?;
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

    pub fn set_stdout(&mut self, out: VmStdout) {
        self.stdout = out;
    }

    pub fn take_stdout(&mut self) -> VmStdout {
        mem::replace(&mut self.stdout, Arc::new(Mutex::new(Box::new(DevNull))))
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
            println!("{i:0>8}    {op} {}", self.get_source(IPtr::from_offset(i)))
        }
        Ok(())
    }

    pub fn dump_fn_code(&self, mut name: SymID) -> Result<()> {
        if let Some(mac_fn) = self.macros.get(&name) {
            name = *mac_fn;
        }
        let func = self.funcs.get(&name).ok_or("No such function")?;
        let start: u32 = func.pos.into();

        let get_jmp = |op: r8c::Op| {
            use r8c::Op::*;
            Some(match op {
                JMP(d) => d,
                JT(d) => d,
                JN(d) => d,
                JZ(d) => d,
                JNZ(d) => d,
                _ => return None,
            })
        };

        let fmt_special = |pos: u32, op: r8c::Op| {
            use r8c::Op::*;
            if let Some(delta) = get_jmp(op) {
                return Some((op.name().to_ascii_lowercase(),
                             vec![self.labels.get(&((pos as i32 + delta) as u32))
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
        for i in start..start+func.sz {
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
                     self.get_source(IPtr::from_offset_u32(i)))?;
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

    pub fn pmem(&self) -> &PMemT {
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
