//! Structured Errors

use crate::nkgc::PV;
use crate::nuke::VTable;
use crate::{Builtin, Sym, SPV};
use crate::r8vm::{ArgSpec, RuntimeError, Traceback, TraceFrame};
use std::backtrace::Backtrace;
use std::borrow::Cow;
use std::mem::{discriminant, replace};
use std::error;
use std::fmt::{self, write, Debug, Display, Write};
use std::num::TryFromIntError;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::mpsc::SendError;

pub type SourceFileName = Option<Cow<'static, str>>;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Source {
    pub file: SourceFileName,
    pub line: u32,
    pub col: u32,
}

impl Source {
    pub fn new(line: u32, col: u32, file: SourceFileName) -> Source {
        Source { file, line, col }
    }

    pub fn none() -> Source {
        Source { file: None, line: 0, col: 0 }
    }

    pub fn with_file(mut self, file: String) -> Source {
        self.file = Some(Cow::from(file));
        self
    }

    pub fn is_none(&self) -> bool {
        self.line == 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceRef<'a> {
    pub file: Option<&'a str>,
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum OpName {
    OpSym(Sym),
    OpStr(&'static str),
    OpBt(Builtin),
}

impl Into<OpName> for Builtin {
    fn into(self) -> OpName {
        OpName::OpBt(self)
    }
}

impl OpName {
    fn name(&self) -> &str {
        match self {
            OpName::OpStr(s) => s,
            OpName::OpSym(s) => s.as_ref(),
            OpName::OpBt(s) => s.as_str(),
        }
    }
}

impl Display for OpName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Copy)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

impl LineCol {
    pub fn into_source(self, file: SourceFileName) -> Source {
        Source { file, line: self.line, col: self.col }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
#[repr(u8)]
pub enum Meta {
    Op(OpName),
    OpArgn(u32),
    OpArgName(OpName),
    VarName(OpName),
    SourceFile(Cow<'static, str>),
    Source(LineCol),
    Related(Option<OpName>, Source),
    Hint(String),
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct MetaSet {
    meta: Vec<Meta>,
}

macro_rules! get_inner_meta {
    ($name:ident, $meta_name:ident, $inner_t:ty) => {
        #[allow(dead_code)]
        fn $name(&self) -> Option<$inner_t> {
            self.meta.iter().find_map(|m| if let Meta::$meta_name(name) = m {
                Some(name)
            } else {
                None
            }).cloned()
        }
    }
}

impl MetaSet {
    /// Add metadata which should replace previous metadata of the same type.
    ///
    /// # Returns
    /// Returns the previous metadata, if it exists.
    fn amend(&mut self, data: Meta) -> Option<Meta> {
        let pos = self.meta.iter()
                           .position(|m| discriminant(m) == discriminant(&data));
        if let Some(idx) = pos {
            Some(replace(&mut self.meta[idx], data))
        } else {
            self.meta.push(data);
            None
        }
    }

    /// Add metadata which should function as a fallback, but should not replace
    /// metadata of the same kind if it exists.
    fn fallback(&mut self, data: Meta) {
        if !self.meta.iter().any(|m| discriminant(m) == discriminant(&data)) {
            self.meta.push(data);
        }
    }

    get_inner_meta!(op, Op, OpName);
    get_inner_meta!(op_argn, OpArgn, u32);
    get_inner_meta!(op_arg_name, OpArgName, OpName);
    get_inner_meta!(src_line_col, Source, LineCol);
    get_inner_meta!(src_file, SourceFile, Cow<'static, str>);
    get_inner_meta!(var_name, VarName, OpName);
    get_inner_meta!(hint, Hint, String);

    fn src(&self) -> Option<Source> {
        let line_col = self.src_line_col()?;
        let file = self.src_file();
        Some(Source {
            file,
            line: line_col.line,
            col: line_col.col,
        })
    }
}

pub struct FmtArgnOp<'a> {
    pre: &'static str,
    post: &'static str,
    meta: &'a MetaSet,
}

impl fmt::Display for FmtArgnOp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(op) = self.meta.op() {
            write!(f, "{}", self.pre)?;
            if let Some(argn) = self.meta.op_argn() {
                write!(f, "for argument {argn} of ({op} ...)")?;
            } else {
                write!(f, "in {op}")?;
            }
            write!(f, "{}", self.post)?;
        } else if let Some(var) = self.meta.var_name() {
            write!(f, "{}for special variable `{}'{}",
                   self.pre, var, self.post)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxErrorKind {
    DotAtEndOfList,
    DotAfterDot,
    SpliceAfterDot,
    ModifierBeforeDot,
    MoreThanOneElemAfterDot,
}

impl fmt::Display for SyntaxErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SyntaxErrorKind::DotAtEndOfList =>
                write!(f, "Dot [.] operator at end of list"),
            SyntaxErrorKind::DotAfterDot =>
                write!(f, "Dot [.] operator immediately after dot [.] operator"),
            SyntaxErrorKind::SpliceAfterDot =>
                write!(f, "Splice operator [,@] after dot operator [.]"),
            SyntaxErrorKind::ModifierBeforeDot =>
                write!(f, "Modifier e.g [,@] [,] [`] or ['] etc. before dot [.] operator e.g (a b ' . c) instead of (a b . 'c)"),
            SyntaxErrorKind::MoreThanOneElemAfterDot =>
                write!(f, "More than one element after dot [.] operator, e.g (1 2 . 3 4) instead of (1 2 3 . 4)"),
        }
    }
}

#[derive(Clone)]
pub struct ExtError(pub Arc<Box<dyn std::error::Error + Send + Sync>>);

impl PartialEq for ExtError {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

#[derive(Clone, PartialEq)]
pub enum ErrorKind {
    SendError { obj_dbg: String },
    STypeError { expect: String, got: String },
    UnexpectedDottedList,
    TypeError { expect: Builtin, got: Builtin },
    NoSuchMethod { strucc: &'static str, method: Sym },
    MutLocked { vt: &'static VTable },
    TypeNError { expect: Vec<Builtin>, got: Builtin },
    ArgTypeError { expect: Vec<Builtin>, got: Vec<Builtin> },
    IfaceNotImplemented { got: Vec<Sym> },
    EnumError { expect: Vec<Sym>, got: Sym },
    ArgError { expect: ArgSpec, got_num: u32 },
    OutsideContext { op: Builtin, ctx: Builtin },
    SyntaxErrorMsg { msg: String },
    LinkError { dst: String, src: usize },
    ConversionError { from: &'static str,
                      to: &'static str,
                      val: String },
    NotEnough { expect: usize,
                got: usize },
    SomeError { msg: String },
    UndefinedHook { name: OpName },
    UndefinedFunction { name: Sym },
    UndefinedVariable { var: Sym },
    ModuleLoadError { lib: Sym },
    ModuleNotFound { lib: Sym },
    Unsupported { op: &'static str },
    Traceback { tb: Box<Traceback> },
    IndexError { idx: usize },
    KeyError { idx: String },
    KeyReference { key: String },
    Exit { status: Sym },
    IOError { kind: std::io::ErrorKind },
    MissingFeature { flag: &'static str },
    CharSpecError { spec: Sym },
    LibError { name: Sym },
    TrailingDelimiter { close: &'static str },
    UnclosedDelimiter { open: &'static str },
    UnlinkedFunction,
    TrailingModifiers { mods: String },
    TrailingEscape,
    NoSuchEscapeChar { chr: char },
    NoSuchField { record: String, field: String },
    UnsupportedOperation { op: OpName },
    DuplicateField { record: String, field: String },
    CannotMoveSharedReference { vt: &'static VTable, nref: u32 },
    ImmovableObject { name: OpName },
    RecordMissingFields { record: String, fields: Vec<String> },
    UnterminatedString,
    MacroexpandRecursionLimit { lim: usize },
    SyntaxError(SyntaxErrorKind),
    IDError { id: usize },
    NoMethodGiven { vt: &'static VTable },
    CloneNotImplemented { obj: OpName },
    Utf8DecodingError,
    None,
    VoidVariable,
    UnknownSetPattern { pat: String },
    Throw { tag: String, obj: String },
    ExtError(ExtError),
}

impl From<std::io::Error> for Error {
    fn from(v: std::io::Error) -> Self {
        Error::new(ErrorKind::IOError { kind: v.kind() })
    }
}

impl From<ErrorKind> for Error {
    fn from(v: ErrorKind) -> Self {
        Error::new(v)
    }
}

impl From<Traceback> for Error {
    fn from(v: Traceback) -> Self {
        let src = v.err.meta().src();
        let e = Error::new(ErrorKind::Traceback { tb: Box::new(v) });
        if let Some(src) = src {
            e.src(src)
        } else {
            e
        }
    }
}

impl From<String> for Error {
    fn from(msg: String) -> Self {
        Error::new(ErrorKind::SomeError { msg })
    }
}

impl From<&str> for Error {
    fn from(msg: &str) -> Self {
        Error::new(ErrorKind::SomeError { msg: msg.to_string() })
    }
}

impl From<RuntimeError> for Error {
    fn from(v: RuntimeError) -> Self {
        Error::new(ErrorKind::SomeError { msg: v.msg })
    }
}

impl From<Error> for RuntimeError {
    fn from(v: Error) -> Self {
        let msg = format!("{}", &v);
        RuntimeError { line: v.meta().src().map(|src| src.line).unwrap_or(0),
                       msg }
    }
}

impl From<ErrorKind> for RuntimeError {
    fn from(v: ErrorKind) -> Self {
        let v: Error = v.into();
        v.into()
    }
}

/// Structural Error Type
#[derive(Clone)]
pub struct Error {
    inner: ErrorInner
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_error(self, f)
    }
}

impl fmt::Debug for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_error(&Error::new(self.clone()), f)
    }
}

#[derive(Clone)]
struct ErrorInner {
    meta: MetaSet,
    ty: ErrorKind,
    rust_trace: Arc<Backtrace>,
}

impl Error {
    pub fn new(kind: ErrorKind) -> Error {
        Error {
            inner: (
                ErrorInner { meta: Default::default(),
                             ty: kind,
                             rust_trace: Arc::new(Backtrace::capture()) }
            )
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self.inner.ty, ErrorKind::None)
    }

    pub fn backtrace(&self) -> Arc<Backtrace> {
        self.inner.rust_trace.clone()
    }

    pub fn kind(&self) -> &ErrorKind {
        &self.inner.ty
    }

    pub fn kind_mut(&mut self) -> &mut ErrorKind {
        &mut self.inner.ty
    }

    pub fn meta(&self) -> &MetaSet {
        &self.inner.meta
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        self.inner.meta == other.inner.meta && self.inner.ty == other.inner.ty
    }
}

pub trait JoinIt {
    fn join(self, sep: impl AsRef<str>) -> String;
}

impl<T, K> JoinIt for K where K: Iterator<Item = T>, T: Display {
    fn join(mut self, sep: impl AsRef<str>) -> String {
        let mut s = String::new();
        let Some(p) = self.next() else { return s };
        write!(s, "{p}").unwrap();
        for p in self {
            write!(s, "{}{p}", sep.as_ref()).unwrap();
        }
        s
    }
}

struct OneOf<'a>(&'a [Builtin]);

impl Display for OneOf<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.len() == 1 {
            write!(f, "{}", self.0[0])
        } else {
            write!(f, "one of {}", self.0.iter().map(|bt| bt.as_str()).join(", "))
        }
    }
}

struct SourceDisplayHack<'a>(&'static str, &'a MetaSet, &'static str);

impl Display for SourceDisplayHack<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(src) = self.1.src() {
            write!(f, "{}{}{}", self.0, src, self.2)
        } else if let Some(srcf) = self.1.src_file() {
            write!(f, "{}[{}]{}", self.0, srcf, self.2)
        } else {
            Ok(())
        }
    }
}

pub trait IsOne {
    fn is_one(&self) -> bool;
}

impl<T> IsOne for T where T: TryInto<i8> + Copy {
    fn is_one(&self) -> bool {
        (*self).try_into().ok().map(|x: i8| x == 1).unwrap_or_default()
    }
}

fn fmt_error(err: &Error, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ErrorKind::*;

    fn plurs(num: impl IsOne) -> &'static str {
        if num.is_one() {""} else {"s"}
    }

    let meta = err.meta();
    match err.kind() {
        TypeError { expect, got } =>
            write!(f, "Type Error: Expected {} {}but got {}",
                   expect.as_str(),
                   FmtArgnOp { pre: "", post: ", ", meta },
                   got.as_str())?,
        STypeError { expect, got } =>
            write!(f, "Type Error: Expected {} {}but got {}",
                   expect,
                   FmtArgnOp { pre: "", post: ", ", meta },
                   got)?,
        TypeNError { expect, got } =>
            write!(f, "Type Error: Expected {} {}but got {}",
                   OneOf(expect),
                   FmtArgnOp { pre: "", post: ", ", meta },
                   got.as_str())?,
        EnumError { expect, got } =>
            write!(f, "Type Error: Expected {:?} {}but got {}",
                   expect, FmtArgnOp { pre: "", post: ", ", meta }, *got)?,
        UnexpectedDottedList => {
            write!(f, "Type Error: Unexpected dotted list")?;
            if let Some(op) = meta.op() {
                write!(f, " given to {}", op.name())?
            }
        }
        ArgError { expect, got_num } => {
            write!(f, "Argument Error: ")?;
            if let Some(op) = meta.op() {
                write!(f, "{} ", op.name())?
            }
            match expect {
                ArgSpec { nargs, nopt: 0, rest: false, .. } =>
                    write!(f, "expected {} argument{}, but got {}",
                            nargs, plurs(*got_num), got_num)?,
                ArgSpec { nargs, nopt, rest: false, .. } =>
                    write!(f, "expected from {} to {} argument{}, but got {}",
                            nargs, nargs+nopt, plurs(*got_num), got_num)?,
                ArgSpec { nargs, rest: true, .. } =>
                    write!(f, "expected at least {} argument{}, but got {}",
                            nargs, plurs(*got_num), got_num)?,
            }
        }
        IfaceNotImplemented { got } => {
            write!(f, "Operation Not Supported: (")?;
            if let Some(op) = meta.op() {
                write!(f, "{}", op.name())?;
            } else {
                write!(f, "?")?;
            }
            for arg in got.iter() {
                write!(f, " {arg}")?;
            }
            write!(f, ")")?;
        }
        ArgTypeError {  expect, got } => {
            write!(f, "Argument Error: ")?;
            if let Some(op) = meta.op() {
                write!(f, "{} ", op.name())?
            }
            write!(f, "expected ({}) but got ({})",
                   expect.iter().map(|s| s.as_str()).join(" "),
                   got.iter().map(|s| s.as_str()).join(" "))?;
        }
        OutsideContext { op, ctx } =>
            write!(f, "Syntax Error: Operator {op} not allowed outside of {ctx} context")?,
        SyntaxErrorMsg { msg } =>
            write!(f, "Syntax Error: {msg}")?,
        ConversionError { from, to, val } =>
            write!(f, "Conversion Error: Could not convert the {from} value `{val}' into {to}")?,
        NotEnough { expect, got } => {
            write!(f, "Stack Error: ")?;
            if let Some(op) = meta.op() {
                write!(f, "Operation `{}' ", op.name())?
            }
            let s = plurs(*got);
            write!(f, "expected {expect} stack element{s}, but got {got}")?;
        }
        SomeError { msg } => write!(f, "Error: {}", msg)?,
        UndefinedHook { name } =>
            write!(f, "Undefined Hook Function: Virtual call to undefined hook function {name}")?,
        UndefinedFunction { name } =>
            write!(f, "Undefined Function: Virtual call to undefined function {name}")?,
        UndefinedVariable { var } =>
            write!(f, "Undefined Variable: {var}")?,
        Unsupported { op } =>
            write!(f, "Unsupported operation: {}", op)?,
        ModuleLoadError { lib } =>
            write!(f, "Module Error: Unable to load module {lib}")?,
        ModuleNotFound { lib } =>
            write!(f, "Module Not Found: Could not find {lib}, check sys/load-path")?,
        ErrorKind::Traceback { tb: _ } => {
            writeln!(f, "Traceback:")?;
            err.write_traceback(f)?;
            return fmt_error(err.cause(), f);
        },
        ErrorKind::IndexError { idx } =>
            write!(f, "Index Error: No such index {idx}")?,
        ErrorKind::Exit { status } =>
            write!(f, "Exit: {status}")?,
        ErrorKind::IOError { kind } => {
            let err: std::io::Error = (*kind).into();
            write!(f, "IOError: {}", err)?;
        }
        CharSpecError { spec } =>
            write!(f, "Invalid char spec `{spec}', use exactly one character in the symbol")?,
        LibError { name } =>
            write!(f, "Error: {name}")?,
        TrailingDelimiter { close } =>
            write!(f, "Trailing Delimiter: Found trailing `{close}' in input")?,
        UnclosedDelimiter { open } =>
            write!(f, "Unclosed Delimiter: Found `{open}' which was not closed in input")?,
        TrailingModifiers { mods } =>
            write!(f, "Trailing Modifiers: Unexpected end of input at: {mods}")?,
        MacroexpandRecursionLimit { lim } =>
            write!(f, "Macro Recursion Error: Macro expansion was recursive beyond {lim} levels")?,
        None => write!(f, "")?,
        SendError { obj_dbg } =>
            write!(f, "Send Error: {obj_dbg}")?,
        LinkError { dst, src: _ } =>
            write!(f, "Link Error: Symbol not found {dst}")?,
        MissingFeature { flag } =>
            write!(f, "Missing Feature: The {flag} feature was not enabled for this version of SPAIK")?,
        SyntaxError(kind) =>
            write!(f, "Syntax Error: {kind}")?,
        IDError { id } =>
            write!(f, "ID Error: id number {id} was out of range for enum")?,
        NoMethodGiven { vt } =>
            write!(f, "No Method Given: No method name was given in method call on {}",
                   vt.type_name)?,
        UnterminatedString =>
            write!(f, "Syntax Error: Unterminated string")?,
        TrailingEscape =>
            write!(f, "Syntax Error: Trailing escape character")?,
        NoSuchEscapeChar { chr } =>
            write!(f, "Syntax Error: No such escape character {chr:?}")?,
        NoSuchField { field, record } =>
            write!(f, "No such field: Record type {record} does not contain {field}")?,
        UnsupportedOperation { op } =>
            write!(f, "Unsupported operation: {}", op)?,
        DuplicateField { field, record } =>
            write!(f, "Duplicate field: Record type {record} initializer has duplicated field {field}")?,
        CannotMoveSharedReference { vt, nref} =>
            write!(f, "Borrow Check Error: cannot move out of shared reference to {}, {} other reference{} exist",
                   vt.type_name, nref - 1, plurs(nref - 1))?,
        ImmovableObject { name } =>
            write!(f, "Borrow Check Error: immovable object type {name}")?,
        MutLocked { vt } =>
            write!(f, "Borrow Check Error: object of type {} is mut-locked by recursive call into VM", vt.type_name)?,
        RecordMissingFields { fields: _, record } =>
            write!(f, "Missing fields: Record type {record} initializer is missing fields")?,
        NoSuchMethod { strucc, method } =>
            write!(f, "No Such Method: ({strucc} {method})")?,
        VoidVariable =>
            write!(f, "Variable is void")?,
        KeyError { idx } =>
            write!(f, "No such key: {idx}")?,
        KeyReference { key } =>
            write!(f, "Reference types cannot be used as keys: {key}")?,
        CloneNotImplemented { obj } =>
            write!(f, "Cannot clone: clone not implemented for type {obj}")?,
        Utf8DecodingError => {
            write!(f, "UTF-8 Encoding Error: ")?
        }
        UnknownSetPattern { pat } =>
            write!(f, "Unknown Set Pattern: {pat}")?,
        Throw { tag, obj } =>
            write!(f, "{tag}: {obj}")?,
        // FIXME: Better error message
        UnlinkedFunction => write!(f, "Unlinked functino")?,
        ExtError(err) => write!(f, "{:?}", err.0)?,
    }

    write!(f, "{}", SourceDisplayHack(" ", meta, ""))?;

    if let Some(hint) = meta.hint() {
        write!(f, " (hint: {hint})")?;
    }

    Ok(())
}

impl Error {
    pub fn src(mut self, src: Source) -> Error {
        self.inner.meta.amend(Meta::Source(LineCol {
            line: src.line,
            col: src.col
        }));
        if let Some(file) = src.file {
            self.inner.meta.amend(Meta::SourceFile(file));
        }
        self
    }

    pub fn see_also(mut self, what: &'static str, src: Source) -> Self {
        self.inner.meta.amend(Meta::Related(Some(OpName::OpStr(what)), src));
        self
    }

    pub fn see_also_sym(mut self, what: impl Into<Sym>, src: Source) -> Self {
        self.inner.meta.amend(Meta::Related(Some(OpName::OpSym(what.into())), src));
        self
    }

    pub fn amend(mut self, meta: Meta) -> Self {
        self.inner.meta.amend(meta);
        self
    }

    pub fn fallback(mut self, meta: Meta) -> Self {
        self.inner.meta.fallback(meta);
        self
    }

    pub fn fop(mut self, new_op: Sym) -> Error {
        self.inner.meta.fallback(Meta::Op(OpName::OpSym(new_op)));
        self
    }

    pub fn bop(mut self, new_op: Builtin) -> Error {
        self.inner.meta.amend(Meta::Op(OpName::OpBt(new_op)));
        self
    }

    pub fn op(mut self, new_op: impl Into<Sym>) -> Error {
        self.inner.meta.amend(Meta::Op(OpName::OpSym(new_op.into())));
        self
    }

    pub fn sop(mut self, new_op: &'static str) -> Error {
        self.inner.meta.amend(Meta::Op(OpName::OpStr(new_op)));
        self
    }

    pub fn also_expected(mut self, ty: Builtin) -> Error {
        match self.inner.ty {
            ErrorKind::TypeError { expect, got } => {
                self.inner.ty = ErrorKind::TypeNError { expect: vec![expect, ty], got }
            }
            ErrorKind::TypeNError { ref mut expect, .. } => {
                expect.push(ty)
            }
            _ => ()
        }
        self
    }

    pub fn argn(mut self, n: u32) -> Error {
        self.inner.meta.amend(Meta::OpArgn(n));
        self
    }

    pub fn arg_name(mut self, n: impl Into<OpName>) -> Error {
        self.inner.meta.amend(Meta::OpArgName(n.into()));
        self
    }

    pub fn cause(&self) -> &Error {
        match self.kind() {
            ErrorKind::Traceback { tb } => {
                tb.err.cause()
            },
            _ => self
        }
    }

    pub fn write_traceback(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let ErrorKind::Traceback { tb } = self.kind() {
            tb.err.write_traceback(f)?;
            for TraceFrame { src, func, args } in tb.frames.iter() {
                write!(f, "  - ({func}")?;
                for arg in args.iter() {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")?;
                writeln!(f, " {}", src)?;
            }
        }
        Ok(())
    }

    pub(crate) fn insert_traceframe(mut self, src: Source, func: OpName, args: &[PV]) -> Self {
        if let ErrorKind::Traceback { ref mut tb } = self.kind_mut() {
            tb.frames.push(TraceFrame {
                src,
                func,
                args: args.iter().map(|v| v.to_string()).collect()
            })
        }
        self
    }
}

impl serde::ser::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error::new(ErrorKind::SomeError { msg: msg.to_string() })
    }
}

impl serde::de::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error::new(ErrorKind::SomeError { msg: msg.to_string() })
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_error(&Error::new(self.clone()), f)
    }
}

impl fmt::Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        if self.line == 0 {
            write!(f, "unknown")?;
        } else {
            if let Some(file) = &self.file {
                write!(f, "{} ", file)?;
            }
            write!(f, "{}:{}", self.line, self.col)?;
        }
        write!(f, "]")
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_error(self, f)
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl<T> From<SendError<T>> for Error where T: Debug {
    fn from(err: SendError<T>) -> Self {
        Error::new(ErrorKind::SendError {
            obj_dbg: format!("{:?}", err.0)
        })
    }
}

impl From<TryFromIntError> for Error {
    fn from(err: TryFromIntError) -> Self {
        Error::new(ErrorKind::SomeError { msg: err.to_string() })
    }
}

impl From<std::convert::Infallible> for Error {
    fn from(_: std::convert::Infallible) -> Self {
        unreachable!();
    }
}

macro_rules! err {
    ($kind:ident, $($init:tt)* ) => {
        Err((crate::error::ErrorKind::$kind { $($init)* }).into())
    };
}

macro_rules! bail {
    (($kind:ident $($init:tt)*)$($extra:tt)*) => {
        return Err({
            let err: $crate::error::Error = (crate::error::ErrorKind::$kind  $($init)* ).into();
            err$($extra)*
        })
    };
    ($kind:ident $($init:tt)*) => {
        return Err((crate::error::ErrorKind::$kind  $($init)* ).into())
    };
}

macro_rules! error {
    ($kind:ident, $($init:tt)* ) => {
        crate::error::Error::new(crate::error::ErrorKind::$kind { $($init)* })
    };
}

macro_rules! err_src {
    ($src:expr, $kind:ident, $($init:tt)* ) => {
        Err(crate::error::Error::new(
            (crate::error::ErrorKind::$kind { $($init)* })
        ).src($src))
    };
}

macro_rules! error_src {
    ($src:expr, $kind:ident, $($init:tt)* ) => {
        crate::error::Error::new(
            (crate::error::ErrorKind::$kind { $($init)* }),
        ).src($src)
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_one() {
        assert!(1i32.is_one());
        assert!(!2i32.is_one());
        assert!(1usize.is_one());
        assert!(!2usize.is_one());
        assert!(1u32.is_one());
        assert!(!2u32.is_one());
    }

    #[test]
    fn file_name_and_hint_but_no_lineno() {
        let err = Error::new(ErrorKind::SomeError { msg: "thing".to_owned() })
            .amend(Meta::SourceFile(Cow::Borrowed("filename")))
            .amend(Meta::Hint("have you tried counseling?".to_owned()));
        assert_eq!(format!("{err}"), "Error: thing [filename] (hint: have you tried counseling?)");
    }
}
