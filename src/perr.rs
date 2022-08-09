//! Parse Errors

use std::fmt;

#[derive(Debug, Eq, PartialEq)]
pub struct ParseErr {
    pub line: u32,
    pub col: u32,
    pub rs_line: u32,
    pub rs_file: &'static str,
    pub msg: String,
}

pub type PResult<T> = Result<T, ParseErr>;

impl fmt::Display for ParseErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Parse Error: {} @({}:{}) (in {}:{})",
            self.msg, self.line, self.col, self.rs_file, self.rs_line
        )
    }
}

#[macro_export]
macro_rules! mperr {
    ( $tok:expr, $msg:literal $(, $fmt_arg:expr)* ) => {
        ParseErr {
            line: $tok.line,
            col: $tok.col,
            msg: format!($msg, $($fmt_arg),*),
            rs_line: line!(),
            rs_file: file!()
        }
    }
}

#[macro_export]
macro_rules! perr {
    ( $msg:expr ) => {
        perr!((0, 0), $msg.to_string())
    };
    ( $line_col:expr, $msg:expr ) => {
        perr!(@new $line_col, $msg.to_string())
    };
    ( $line_col:expr, $msg:expr, $($fmt_arg:expr),+ ) => {
        perr!(@new $line_col, format!($msg, $($fmt_arg),+))
    };
    ( @new $line_col:expr, $msg:expr ) => {
        return Err(ParseErr {
            line: $line_col.0,
            col: $line_col.1,
            msg: $msg,
            rs_line: line!(),
            rs_file: file!(),
        })
    };
}
