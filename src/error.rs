//! Structured Errors

use num_traits::PrimInt as Integer;

use crate::Builtin;
use crate::perr::ParseErr;
use crate::r8vm::{ArgSpec, RuntimeError, Traceback, TraceFrame};
use crate::nkgc::SymID;
use crate::fmt::LispFmt;
use crate::sym_db::{SymDB, SYM_DB};
use std::backtrace::Backtrace;
use std::borrow::Cow;
use std::mem::{discriminant, replace};
use std::error;
use std::fmt::{self, Debug};
use std::num::TryFromIntError;
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum OpName {
    OpSym(SymID),
    OpStr(&'static str),
    OpBt(Builtin),
}

impl OpName {
    fn name<'a>(&self, db: &'a dyn SymDB) -> Cow<'a, str> {
        match self {
            OpName::OpStr(s) => Cow::Borrowed(s),
            OpName::OpSym(s) => db.name(*s),
            OpName::OpBt(s) => db.name(s.sym()),
        }
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

pub struct FmtArgnOp<'a, 'b> {
    pre: &'static str,
    post: &'static str,
    meta: &'a MetaSet,
    db: &'b dyn SymDB,
}

impl fmt::Display for FmtArgnOp<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(op) = self.meta.op() {
            write!(f, "{}", self.pre)?;
            if let Some(argn) = self.meta.op_argn() {
                write!(f, "for argument {argn} of ({} ...)", op.name(self.db))?;
            } else {
                write!(f, "in {}", op.name(self.db))?;
            }
            write!(f, "{}", self.post)?;
        } else if let Some(var) = self.meta.var_name() {
            write!(f, "{}for special variable `{}'{}",
                   self.pre, var.name(self.db), self.post)?;
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
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ErrorKind {
    SendError { obj_dbg: String },
    STypeError { expect: String, got: String },
    UnexpectedDottedList,
    TypeError { expect: Builtin, got: Builtin },
    TypeNError { expect: Vec<Builtin>, got: Builtin },
    ArgTypeError { expect: Vec<Builtin>, got: Vec<Builtin> },
    IfaceNotImplemented { got: Vec<SymID> },
    EnumError { expect: Vec<SymID>, got: SymID },
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
    UndefinedFunction { name: SymID },
    UndefinedVariable { var: SymID },
    ModuleLoadError { lib: SymID },
    ModuleNotFound { lib: SymID },
    Unsupported { op: &'static str },
    Traceback { tb: Box<Traceback> },
    IndexError { idx: usize },
    Exit { status: SymID },
    IOError { kind: std::io::ErrorKind },
    MissingFeature { flag: &'static str },
    CharSpecError { spec: SymID },
    LibError { name: SymID },
    TrailingDelimiter { close: &'static str },
    UnclosedDelimiter { open: &'static str },
    TrailingModifiers { mods: String },
    MacroexpandRecursionLimit { lim: usize },
    SyntaxError(SyntaxErrorKind),
    IDError { id: usize },
    None,
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
#[derive(Debug, Clone)]
pub struct Error {
    inner: ErrorInner
}

#[derive(Debug, Clone)]
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

    pub fn meta(&self) -> &MetaSet {
        &self.inner.meta
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        self.inner.meta == other.inner.meta && self.inner.ty == other.inner.ty
    }
}

fn fmt_error(err: &Error, f: &mut fmt::Formatter<'_>, db: &dyn SymDB) -> fmt::Result {
    use ErrorKind::*;
    let nameof = |sym| db.name(sym);

    fn plurs(num: impl Integer) -> &'static str {
        if num.is_one() {""} else {"s"}
    }

    let meta = err.meta();
    match err.kind() {
        TypeError { expect, got } =>
            write!(f, "Type Error: Expected {} {}but got {}",
                   nameof(expect.sym()),
                   FmtArgnOp { pre: "", post: ", ", db, meta },
                   nameof(got.sym()))?,
        STypeError { expect, got } =>
            write!(f, "Type Error: Expected {} {}but got {}",
                   expect,
                   FmtArgnOp { pre: "", post: ", ", db, meta },
                   got)?,
        TypeNError { expect, got } =>
            write!(f, "Type Error: Expected one of ({}) {}but got {}",
                   expect.iter().map(|v| nameof(v.sym())).collect::<Vec<_>>().join(", "),
                   FmtArgnOp { pre: "", post: ", ", db, meta },
                   nameof(got.sym()))?,
        EnumError { expect, got } =>
            write!(f, "Type Error: Expected {:?} {}but got {}",
                   expect.iter().copied().map(nameof).collect::<Vec<_>>(),
                   FmtArgnOp { pre: "", post: ", ", db, meta },
                   nameof(*got))?,
        UnexpectedDottedList => {
            write!(f, "Type Error: Unexpected dotted list")?;
            if let Some(op) = meta.op() {
                write!(f, " given to {}", op.name(db))?
            }
        }
        ArgError { expect, got_num } => {
            write!(f, "Argument Error: ")?;
            if let Some(op) = meta.op() {
                write!(f, "{} ", op.name(db))?
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
                write!(f, "{}", op.name(db))?;
            } else {
                write!(f, "?")?;
            }
            for arg in got.iter() {
                write!(f, " {}", nameof(*arg))?;
            }
            write!(f, ")")?;
        }
        ArgTypeError {  expect, got } => {
            write!(f, "Argument Error: ")?;
            if let Some(op) = meta.op() {
                write!(f, "{} ", op.name(db))?
            }
            write!(f, "expected ({}) but got ({})",
                   expect.iter().copied().map(|s| nameof(s.sym())).collect::<Vec<_>>().join(" "),
                   got.iter().copied().map(|s| nameof(s.sym())).collect::<Vec<_>>().join(" "))?;
        }
        OutsideContext { op, ctx } =>
            write!(f, "Syntax Error: Operator {} not allowed outside of {} context",
                   nameof(op.sym()), nameof(ctx.sym()))?,
        SyntaxErrorMsg { msg } =>
            write!(f, "Syntax Error: {}", msg)?,
        ConversionError { from, to, val } =>
            write!(f, "Conversion Error: Could not convert the {} value `{}' into {}",
                    from, val, to)?,
        NotEnough { expect, got } => {
            write!(f, "Stack Error: ")?;
            if let Some(op) = meta.op() {
                write!(f, "Operation `{}' ", op.name(db))?
            }
            write!(f, "expected {} stack element{}, but got {}",
                   expect, plurs(*got), got)?;
        }
        SomeError { msg } => write!(f, "Error: {}", msg)?,
        UndefinedFunction { name } =>
            write!(f, "Undefined Function: Virtual call to undefined function {}",
                   nameof(*name))?,
        UndefinedVariable { var } =>
            write!(f, "Undefined Variable: {}", nameof(*var))?,
        Unsupported { op } =>
            write!(f, "Unsupported operation: {}", op)?,
        ModuleLoadError { lib } =>
            write!(f, "Module Error: Unable to load module {}", nameof(*lib))?,
        ModuleNotFound { lib } =>
            write!(f, "Module Not Found: Could not find {}, check sys/load-path", nameof(*lib))?,
        ErrorKind::Traceback { tb } => {
            writeln!(f, "Traceback:")?;
            for TraceFrame { src, func, args } in tb.frames.iter() {
                write!(f, "  - ({}", nameof(*func))?;
                let mut it = args.iter().peekable();
                if it.peek().is_some() {
                    write!(f, " ")?;
                }
                while let Some(arg) = it.next() {
                    write!(f, "{}", arg.lisp_to_string(db))?;
                    if it.peek().is_some() {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")?;
                writeln!(f, " {}", src)?;
            }
            return fmt_error(&tb.err, f, db)
        },
        ErrorKind::IndexError { idx } =>
            write!(f, "Index Error: No such index {}", idx)?,
        ErrorKind::Exit { status } =>
            write!(f, "Exit: {}", nameof(*status))?,
        ErrorKind::IOError { kind } => {
            let err: std::io::Error = (*kind).into();
            write!(f, "IOError: {}", err)?;
        }
        CharSpecError { spec } =>
            write!(f, "Invalid char spec `{}', use exactly one character in the symbol",
                   nameof(*spec))?,
        LibError { name } =>
            write!(f, "Error: {}", nameof(*name))?,
        TrailingDelimiter { close } =>
            write!(f, "Trailing Delimiter: Found trailing `{}' in input", close)?,
        UnclosedDelimiter { open } =>
            write!(f, "Unclosed Delimiter: Found `{}' which was not closed in input", open)?,
        TrailingModifiers { mods } =>
            write!(f, "Trailing Modifiers: Unexpected end of input at: {}", mods)?,
        MacroexpandRecursionLimit { lim } =>
            write!(f, "Macro Recursion Error: Macro expansion was recursive beyond {} levels", lim)?,
        None => write!(f, "")?,
        SendError { obj_dbg } =>
            write!(f, "Send Error: {obj_dbg}")?,
        LinkError { dst, src: _ } =>
            write!(f, "Link Error: Symbol not found {dst}")?,
        MissingFeature { flag } =>
            write!(f, "Missing Feature: The {} feature was not enabled for this version of SPAIK", flag)?,
        SyntaxError(kind) =>
            write!(f, "Syntax Error: {}", kind)?,
        IDError { id } =>
            write!(f, "ID Error: id number {id} was out of range for enum")?,
    }

    if let Some(src) = meta.src() {
        write!(f, " {}", src)?;
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

    pub fn see_also_sym(mut self, what: SymID, src: Source) -> Self {
        self.inner.meta.amend(Meta::Related(Some(OpName::OpSym(what)), src));
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

    pub fn fop(mut self, new_op: SymID) -> Error {
        self.inner.meta.fallback(Meta::Op(OpName::OpSym(new_op)));
        self
    }

    pub fn bop(mut self, new_op: Builtin) -> Error {
        self.inner.meta.amend(Meta::Op(OpName::OpBt(new_op)));
        self
    }

    pub fn op(mut self, new_op: SymID) -> Error {
        self.inner.meta.amend(Meta::Op(OpName::OpSym(new_op)));
        self
    }

    pub fn argn(mut self, n: u32) -> Error {
        self.inner.meta.amend(Meta::OpArgn(n));
        self
    }

    pub fn cause(&self) -> &Error {
        match self.kind() {
            ErrorKind::Traceback { tb } => {
                &tb.err
            },
            _ => self
        }
    }

    /**
    ** Get a string representation of the Error object.
    **
    ** # Arguments
    **
    ** - `mem` : If provided, this is used to retrieve symbol strings.
    */
    pub fn to_string(&self, db: &dyn SymDB) -> String {
        format!("{}", {
            struct PVFmtWrap<'a, 'b> {
                val: &'b Error,
                db: &'a dyn SymDB
            }

            impl fmt::Display for PVFmtWrap<'_, '_> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    fmt_error(self.val, f, self.db)
                }
            }

            PVFmtWrap { val: self, db }
        })
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
        fmt_error(&Error::new(self.clone()), f, &SYM_DB)
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
        fmt_error(self, f, &SYM_DB)
    }
}

impl error::Error for ErrorKind {}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(self.kind())
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

impl From<ParseErr> for Error {
    fn from(perr: ParseErr) -> Self {
        Error::new(
            ErrorKind::SyntaxErrorMsg { msg: perr.msg },
        ).amend(Meta::Source(LineCol { line: perr.line, col: perr.col }))
    }
}

macro_rules! err {
    ($kind:ident, $($init:tt)* ) => {
        Err((crate::error::ErrorKind::$kind { $($init)* }).into())
    };
}

macro_rules! bail {
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
