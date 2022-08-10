#![allow(clippy::trivial_regex)]
// FIXME: Write documentation for the unsafe functions.
#![allow(clippy::missing_safety_doc)]

#[macro_use]
extern crate lazy_static;
#[allow(unused_imports)]
#[macro_use]
extern crate log;
#[macro_use]
pub mod error;
#[macro_use]
pub(crate) mod utils;
#[macro_use]
pub(crate) mod perr;
#[macro_use]
pub mod chasm;
#[macro_use]
pub mod nkgc;
#[macro_use]
pub mod r8vm;
#[macro_use]
pub(crate) mod ast;
pub(crate) mod sintern;
pub(crate) mod fmt;
pub(crate) mod sym_db;
pub(crate) mod subrs;
pub mod compile;
pub mod sexpr_parse;
//pub(crate) mod tests;
pub(crate) mod tok;
pub mod nuke;
pub(crate) mod module;
pub mod spaik;
#[cfg(feature = "repl")]
pub mod repl;
//pub mod asm_parse;
//pub mod arg_parse_tests;
