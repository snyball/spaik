//! Interactive Read-Eval-Print-Loop

use spaik::repl::REPL;
use std::fmt;
use std::sync::Mutex;
use lazy_static::lazy_static;
use std::io;
use std::os::raw::{c_char, c_void};

extern {
    fn xtermjs_write_stdout(ptr: *const c_char, sz: usize);
    fn xtermjs_write_stderr(ptr: *const c_char, sz: usize);
    // fn xterm_read_stdin(ptr: *const c_char, sz: usize);
}

fn wrap_xtermjs_write_stdout(buf: &[u8]) -> io::Result<()> {
    unsafe {
        xtermjs_write_stdout(buf.as_ptr() as *const c_char, buf.len());
    }
    Ok(())
}

// type WriteFn = fn(&[u8]) -> io::Result<()>;
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

lazy_static! {
    static ref GLOBAL_REPL: Mutex<REPL> =
        Mutex::new(
            REPL::new(
                Some(
                    Box::new(
                        FnFlushWriter::new(
                            WriteFn(wrap_xtermjs_write_stdout))))
            ).unwrap());
}

#[no_mangle]
pub extern fn repl_reset() {
    let mut repl = GLOBAL_REPL.lock().unwrap();
    *repl =
        REPL::new(
            Some(
                Box::new(
                    FnFlushWriter::new(
                        WriteFn(wrap_xtermjs_write_stdout))))).unwrap();
}

#[no_mangle]
pub extern fn repl_eval(code: &str) {
    GLOBAL_REPL.lock().unwrap().eval(code);
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}
