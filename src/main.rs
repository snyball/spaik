#![allow(unused_imports)]
#[macro_use]
extern crate spaik;
use spaik::perr::*;
use spaik::r8vm::*;
use spaik::nkgc::{SymID, PV};
use spaik::error::Error;
use std::env;
use std::ffi::OsStr;
use std::fs::File;
use std::io::prelude::*;
use std::io;
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut f: Box<dyn Read> = match &args[..] {
        [file] => Box::new(File::open(file)?),
        [] => Box::new(io::stdin()),
        _ => panic!("Invalid arguments: {:?}", args),
    };
    let mut code = String::new();
    if f.read_to_string(&mut code).is_err() {
        return Ok(())
    }
    let mut vm = R8VM::new();
    match vm.eval(&code) {
        Ok(_) => (),
        Err(e) => println!("{}", e.to_string(&vm)),
    }

    Ok(())
}
