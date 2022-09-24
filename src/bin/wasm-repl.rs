//! Interactive Read-Eval-Print-Loop

// extern crate console_error_panic_hook;

use spaik::repl::REPL;
use core::slice;
use std::alloc::Layout;
use std::fmt;
use std::sync::Mutex;
use lazy_static::lazy_static;
use std::io;
use std::os::raw::{c_char, c_void};
use std::panic;

#[allow(dead_code)]
extern "C" {
    fn xtermjs_write_stdout(ptr: *const c_char, sz: usize);
    fn console_error(ptr: *const c_char, sz: usize);
    fn console_log(ptr: *const c_char, sz: usize);
}

fn wrap_xtermjs_write_stdout(buf: &[u8]) -> io::Result<()> {
    unsafe {
        xtermjs_write_stdout(buf.as_ptr() as *const c_char, buf.len());
    }
    Ok(())
}

struct WriteFn(fn(&[u8]) -> io::Result<()>);

impl fmt::Debug for WriteFn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<WriteFn: {:?}>", self.0 as *const c_void)
    }
}

#[derive(Debug)]
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
            (self.writefn.0)(first)?;
            self.buffer.drain(..=i).for_each(drop);
        }

        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        (self.writefn.0)(&self.buffer)?;
        self.buffer.clear();

        Ok(())
    }
}

pub fn new_wasm_repl() -> REPL {
    REPL::new(
        Some(Box::new(FnFlushWriter::new(WriteFn(wrap_xtermjs_write_stdout))))
    ).unwrap()
}

lazy_static! {
    static ref GLOBAL_REPL: Mutex<REPL> = Mutex::new(new_wasm_repl());
}

#[no_mangle]
pub extern fn repl_reset() {
    let mut repl = GLOBAL_REPL.lock().unwrap();
    *repl = new_wasm_repl();
}

#[no_mangle]
pub extern fn repl_eval(ptr: *const c_char, sz: usize) {
    let code = unsafe {
        String::from_utf8_lossy(slice::from_raw_parts(ptr as *const u8, sz))
    };
    GLOBAL_REPL.lock().unwrap().eval(code.as_ref());
}

#[no_mangle]
pub extern fn alloc(sz: usize) -> *mut u8 {
    unsafe {
        std::alloc::alloc(Layout::from_size_align(sz, 1).unwrap())
    }
}

#[no_mangle]
pub extern fn dealloc(ptr: *mut u8, sz: usize) {
    unsafe {
        std::alloc::dealloc(ptr, Layout::from_size_align(sz, 1).unwrap());
    }
}

pub fn panic_hook(info: &panic::PanicInfo) {
    let msg = format!("Error: {}", info.to_string());
    unsafe {
        console_error(msg.as_ptr() as *const c_char, msg.len());
    }
}

#[no_mangle]
pub extern fn init() {
    panic::set_hook(Box::new(panic_hook));
    colored::control::set_override(true);
    GLOBAL_REPL.lock().unwrap().print_intro();
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}
