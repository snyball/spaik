//! Structured Errors

use crate::perr::ParseErr;
use crate::r8vm::{ArgSpec, RuntimeError, Traceback, TraceFrame};
use crate::r8vm::r8c::Op as R8C;
use crate::nkgc::SymID;
use crate::ast::Value;
use crate::fmt::LispFmt;
use crate::sym_db::{SymDB, SYM_DB};
use std::result;
use std::error;
use std::fmt;
use std::num::TryFromIntError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source {
    pub file: Option<String>,
    pub line: u32,
    pub col: u32,
}

impl Source {
    pub fn new(line: u32, col: u32) -> Source {
        Source { file: None, line, col }
    }

    pub fn none() -> Source {
        Source { file: None, line: 0, col: 0 }
    }

    pub fn with_file(mut self, file: String) -> Source {
        self.file = Some(file);
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

#[derive(Debug, Clone, PartialEq)]
pub enum ErrorKind {
    IllegalInstruction { inst: R8C },
    TypeError { expect: SymID, got: SymID, op: SymID, argn: u32 },
    TypeNError { expect: Vec<SymID>, got: SymID, op: SymID, argn: u32 },
    ArgTypeError { expect: Vec<SymID>, got: Vec<SymID>, op: SymID },
    EnumError { expect: Vec<SymID>, got: SymID, op: SymID, argn: u32 },
    ArgError { expect: ArgSpec, got_num: u32, op: SymID },
    OutsideContext { op: SymID, ctx: SymID },
    SyntaxError { msg: String },
    LinkError { dst: String, src: usize },
    IDError { id: usize },
    ConversionError { from: &'static str,
                      to: &'static str,
                      val: String },
    NotEnough { expect: usize,
                got: usize,
                op: &'static str },
    SomeError { msg: String },
    UndefinedFunction { name: SymID },
    UndefinedVariable { var: SymID },
    UndefinedFunctionString { name: String },
    UndefinedVariableString { name: String },
    ModuleLoadError { lib: SymID },
    Unsupported { op: &'static str },
    IllegalVariableDeclaration { decl: Value },
    Traceback { tb: Box<Traceback> },
    IndexError { idx: usize },
    Exit { status: SymID },
    IOError { kind: std::io::ErrorKind },
    MissingFeature { flag: &'static str },
    CharSpecError { spec: SymID },
}

impl From<std::io::Error> for Error {
    fn from(v: std::io::Error) -> Self {
        Error { src: None, ty: ErrorKind::IOError { kind: v.kind() } }
    }
}

impl From<ErrorKind> for Error {
    fn from(v: ErrorKind) -> Self {
        Error { src: None, ty: v }
    }
}

impl From<Traceback> for Error {
    fn from(v: Traceback) -> Self {
        Error { src: v.err.src.clone(),
                ty: ErrorKind::Traceback { tb: Box::new(v) } }
    }
}

impl From<String> for Error {
    fn from(msg: String) -> Self {
        Error { src: None, ty: ErrorKind::SomeError { msg } }
    }
}

impl From<&str> for Error {
    fn from(msg: &str) -> Self {
        Error { src: None,
                ty: ErrorKind::SomeError { msg: msg.to_string() } }
    }
}

impl From<RuntimeError> for Error {
    fn from(v: RuntimeError) -> Self {
        Error { src: Some(Source { line: v.line, col: 0, file: None }),
                ty: ErrorKind::SomeError { msg: v.msg } }
    }
}

impl From<Error> for RuntimeError {
    fn from(v: Error) -> Self {
        let msg = format!("{}", &v);
        RuntimeError { line: v.src.map(|src| src.line).unwrap_or(0),
                       msg }
    }
}

impl From<ErrorKind> for RuntimeError {
    fn from(v: ErrorKind) -> Self {
        let v: Error = v.into();
        v.into()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    pub src: Option<Source>,
    pub ty: ErrorKind,
}

fn fmt_error(err: &Error, f: &mut fmt::Formatter<'_>, db: &dyn SymDB) -> fmt::Result {
    use ErrorKind::*;
    let nameof = |sym| db.name(sym);
    let tostring = |v: &Value| v.to_string(db);
    match &err.ty {
        IllegalInstruction { inst } =>
            write!(f, "Illegal instruction: <{}>", inst)?,
        TypeError { expect, got, op, argn } =>
            write!(f, "Type Error: Expected {} for argument {} of ({} ...), but got {}",
                   nameof(*expect), argn, nameof(*op), nameof(*got))?,
        TypeNError { expect, got, op, argn } =>
            write!(f, "Type Error: Expected one of {} for argument {} of ({} ...), but got {}",
                   {
                       expect.iter()
                             .map(|v| nameof(*v))
                             .collect::<Vec<_>>()
                             .join(", ")
                   },
                   argn, nameof(*op), nameof(*got))?,
        EnumError { expect, got, op, argn } =>
            write!(f, "Argument Error: Expected one of {:?} for argument {} of ({} ...), but got {}",
                   expect.iter().copied().map(nameof).collect::<Vec<_>>(),
                   argn, nameof(*op), nameof(*got))?,
        ArgError { expect, got_num, op } => {
            write!(f, "Argument Error: ({} ...) ", nameof(*op))?;
            match expect {
                ArgSpec { nargs, nopt: 0, rest: false, .. } =>
                    write!(f, "expected {} arguments, but got {}",
                            nargs, got_num)?,
                ArgSpec { nargs, nopt, rest: false, .. } =>
                    write!(f, "expected from {} to {} arguments, but got {}",
                            nargs, nargs+nopt, got_num)?,
                ArgSpec { nargs, rest: true, .. } =>
                    write!(f, "expected at least {} arguments, but got {}",
                            nargs, got_num)?,
            }
        }
        ArgTypeError {  expect, got, op  } =>
            write!(f, "Argument Error: ({} ...) expected ({}) but got ({})",
                   nameof(*op),
                   expect.iter().copied().map(nameof).collect::<Vec<_>>().join(" "),
                   got.iter().copied().map(nameof).collect::<Vec<_>>().join(" "))?,
        OutsideContext { op, ctx } =>
            write!(f, "Syntax Error: Operator {} not allowed outside of {} context",
                   nameof(*op), nameof(*ctx))?,
        SyntaxError { msg } =>
            write!(f, "Syntax Error: {}", msg)?,
        //LinkError
        //IDError
        ConversionError { from, to, val } =>
            write!(f, "Conversion Error: Could not convert the {} value `{}' into {}",
                    from, val, to)?,
        NotEnough { expect, got, op } =>
            write!(f, "Stack Error: Operation `{}' expected {} elements, but got {}",
                    op, expect, got)?,
        SomeError { msg } => write!(f, "Error: {}", msg)?,
        UndefinedFunction { name } =>
            write!(f, "Undefined Function: Virtual call to undefined function '{}'",
                   nameof(*name))?,
        UndefinedVariable { var } =>
            write!(f, "Undefined Variable: {}", nameof(*var))?,
        Unsupported { op } =>
            write!(f, "Unsupported operation: {}", op)?,
        ModuleLoadError { lib } =>
            write!(f, "Module Error: Unable to load module {}", nameof(*lib))?,
        IllegalVariableDeclaration { decl } =>
            write!(f, "Syntax Error: Illegal variable declaration: {}",
                   tostring(decl))?,
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
            fmt_error(&tb.err, f, db)?;
        },
        ErrorKind::IndexError { idx } =>
            write!(f, "Index Error: No such index {}", idx)?,
        ErrorKind::Exit { status } =>
            write!(f, "Exit: {}", nameof(*status))?,
        ErrorKind::IOError { kind } => {
            let err: std::io::Error = (*kind).into();
            write!(f, "IOError: {}", err)?;
        }
        ErrorKind::MissingFeature { flag } =>
            write!(f, "Missing Feature: {}", flag)?,
        CharSpecError { spec } =>
            write!(f, "Invalid char spec `{}', use exactly one character in the symbol",
                   nameof(*spec))?,
        x => unimplemented!("{:?}", x),
    }
    if let Some(src) = &err.src {
        if !src.is_none() {
            write!(f, " {}", src)?;
        }
    } else {
        // write!(f, " [@unknown]")?;
    }
    Ok(())
}

impl Error {
    pub fn with_src(mut self, src: Source) -> Error {
        self.src = Some(src);
        self
    }

    pub fn op(mut self, new_op: SymID) -> Error {
        match &mut self.ty {
            ErrorKind::TypeError { ref mut op, .. } => *op = new_op,
            ErrorKind::TypeNError { ref mut op, .. } => *op = new_op,
            ErrorKind::ArgTypeError { ref mut op, .. } => *op = new_op,
            ErrorKind::EnumError { ref mut op, .. } => *op = new_op,
            ErrorKind::ArgError { ref mut op, .. } => *op = new_op,
            ErrorKind::OutsideContext { ref mut op, .. } => *op = new_op,
            _ => (),
        }
        self
    }

    pub fn argn(mut self, n: u32) -> Error {
        match &mut self.ty {
            ErrorKind::TypeError { ref mut argn, .. } => *argn = n,
            ErrorKind::TypeNError { ref mut argn, .. } => *argn = n,
            _ => ()
        }
        self
    }

    pub fn cause(&self) -> &Error {
        match &self.ty {
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

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {
        fmt_error(&Error { ty: self.clone(), src: None }, f, &SYM_DB)
    }
}

impl fmt::Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {
        write!(f, "[@")?;
        if self.line == 0 {
            write!(f, "unknown")?;
        } else {
            if let Some(file) = &self.file {
                write!(f, "{}-", file)?;
            }
            write!(f, "{}:{}", self.line, self.col)?;
        }
        write!(f, "]")
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {
        fmt_error(self, f, &SYM_DB)
    }
}

impl error::Error for ErrorKind {}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.ty)
    }
}

impl From<TryFromIntError> for Error {
    fn from(err: TryFromIntError) -> Self {
        Error {
            src: None,
            ty: ErrorKind::SomeError { msg: err.to_string() }
        }
    }
}

impl From<std::convert::Infallible> for Error {
    fn from(_: std::convert::Infallible) -> Self {
        unreachable!();
    }
}

impl From<ParseErr> for Error {
    fn from(perr: ParseErr) -> Self {
        Error {
            src: Some(Source {
                file: None,
                line: perr.line as u32,
                col: perr.col as u32,
            }),
            ty: ErrorKind::SyntaxError { msg: perr.msg }
        }
    }
}

macro_rules! err {
    ($kind:ident, $($init:tt)* ) => {
        Err((crate::error::ErrorKind::$kind { $($init)* }).into())
    };
}

macro_rules! error {
    ($kind:ident, $($init:tt)* ) => {
        crate::error::Error {
            src: None,
            ty: crate::error::ErrorKind::$kind { $($init)* },
        }
    };
}

macro_rules! err_src {
    ($src:expr, $kind:ident, $($init:tt)* ) => {
        Err(crate::error::Error { src: Some($src), ty: (crate::error::ErrorKind::$kind { $($init)* }) })
    };
}

macro_rules! error_src {
    ($src:expr, $kind:ident, $($init:tt)* ) => {
        crate::error::Error { src: Some($src), ty: (crate::error::ErrorKind::$kind { $($init)* }) }
    };
}
