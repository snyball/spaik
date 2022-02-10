#![allow(clippy::trivial_regex)]
// FIXME: Write documentation for the unsafe functions.
#![allow(clippy::missing_safety_doc)]

#[allow(non_upper_case_globals)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
pub mod nk {
    include!(concat!(env!("OUT_DIR"), "/nuke-sys.rs"));
}

#[cfg(feature = "repl")]
extern crate prettytable;
#[macro_use]
extern crate lazy_static;
#[allow(unused_imports)]
#[macro_use]
extern crate log;
extern crate binwrite;
extern crate binread;
#[macro_use]
pub mod error;
#[macro_use]
pub mod utils;
#[macro_use]
pub mod perr;
#[macro_use]
pub mod chasm;
#[macro_use]
pub mod nkgc;
#[macro_use]
pub mod r8vm;
#[macro_use]
pub mod ast;
pub mod sintern;
pub mod fmt;
pub mod sym_db;
pub mod subrs;
pub mod compile;
pub mod sexpr_parse;
//pub mod tests;
pub mod tok;
pub mod nuke;
pub mod module;
#[cfg(feature = "repl")]
pub mod repl;
//pub mod asm_parse;
//pub mod arg_parse_tests;
