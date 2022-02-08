//! Interactive Read-Eval-Print-Loop

use rustyline::error::ReadlineError;
use rustyline::Editor;
use spaik::r8vm::R8VM;
use spaik::nkgc::PV;
use spaik::compile::Builtin;
use spaik::error::{Error, ErrorKind};
use spaik::fmt::LispFmt;
use spaik::repl::REPL;
use std::process;
use std::fs;
use std::sync::Mutex;
use colored::*;
use lazy_static::lazy_static;
use wasm_bindgen::prelude::*;
use std::io;
use std::os::raw::c_char;

extern {
    fn xtermjs_write_stdout(ptr: *const c_char, sz: usize);
    fn xtermjs_write_stderr(ptr: *const c_char, sz: usize);
    // fn xterm_read_stdin(ptr: *const c_char, sz: usize);
}

type WriteFn = fn(&[u8]) -> io::Result<()>;

struct FnFlushWriter {
    writefn: WriteFn,
    buffer: Vec<u8>,
}

impl FnFlushWriter {
    fn new(writefn: WriteFn) -> FnFlushWriter {
        FnFlushWriter {
            buffer: Vec::new(),
            writefn,
        }
    }
}

impl io::Write for FnFlushWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.buffer.extend(buf);

        if let Some(i) = self.buffer.iter().rposition(|x| *x == b'\n') {
            let (first, _last) = self.buffer.split_at(i+1);
            (self.writefn)(first)?;
            self.buffer.drain(..=i).for_each(drop);
        }

        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        (self.writefn)(&self.buffer)?;
        self.buffer.clear();

        Ok(())
    }
}

lazy_static! {
    static ref GLOBAL_REPL: Mutex<REPL<'static>> =
        Mutex::new(
            REPL::new(
                Some(FnFlushWriter::new(xtermjs_write_stdout))
            ).unwrap());
}

#[wasm_bindgen]
fn reset() -> bool {
    let repl = GLOBAL_REPL.lock().unwrap();
    *repl = REPL::new(Some(FnFlushWriter::new(xtermjs_write_stdout))).unwrap();
    true
}

#[wasm_bindgen]
fn eval(code: &str) -> Result<String, String> {
    GLOBAL_REPL.lock().unwrap().eval(code)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
}
