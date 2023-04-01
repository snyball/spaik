//! Interactive Read-Eval-Print-Loop

#[cfg(feature = "readline")]
use rustyline::{Editor, error::ReadlineError};
#[cfg(feature = "readline")]
use std::{process, fs};
use crate::r8vm::{R8VM, OutStream};
use crate::nkgc::PV;
use crate::compile::Builtin;
use crate::error::{Error, ErrorKind};
use crate::fmt::LispFmt;
use std::path::Path;
use crate::stylize::Stylize;

#[allow(unused)]
fn make_intro() -> String {
    format!("{read} {arrow} {eval} {arrow} {print} {arrow} {loop}
 ┗━━━━━━━━━━━━━━━━━━━━━━┛\n",
            read="read".style_ret(),
            eval="eval".style_ret(),
            print="print".style_ret(),
            loop="loop".style_ret(),
            arrow="➟"
    )
}

macro_rules! vmprint {
    ($vm:expr, $($fmt:expr),+) => {
        $vm.print_fmt(format_args!($($fmt),+)).unwrap()
    };
}

macro_rules! vmprintln {
    ($vm:expr, $($fmt:expr),+) => {
        $vm.print_fmt(format_args!($($fmt),+)).unwrap();
        $vm.println(&"").unwrap();
    };
}

type EBResult<T> = Result<T, Box<dyn std::error::Error>>;

pub trait LineInput {
    fn readline();
    fn save_history<P: AsRef<Path> + ?Sized>(&self, path: &P) -> EBResult<()>;
    fn load_history<P: AsRef<Path> + ?Sized>(&mut self, path: &P) -> EBResult<()>;
    fn add_history_entry<S: AsRef<str> + Into<String>>(&mut self, line: S) -> bool;
}

pub struct REPL {
    vm: R8VM,
    exit_status: Option<i32>,
}

impl REPL {
    pub fn new(out_override: Option<Box<dyn OutStream>>) -> Result<REPL, Error> {
        let mut vm = R8VM::new();
        if let Some(out) = out_override {
            vm.set_stdout(out);
        }
        Ok(REPL {
            vm,
            exit_status: None,
        })
    }

    pub fn eval(&mut self, code: &str) {
        match self.vm.eval(code) {
            Ok(PV::Nil) => {}
            Ok(res) => {
                vmprint!(self.vm, "{}", "=> ".style_ret());
                vmprintln!(self.vm, "{}", res.lisp_to_string(&self.vm));
            },
            Err(e) => {
                match e.cause() {
                    Error { ty: ErrorKind::Exit { status }, ..} => {
                        use Builtin::*;
                        self.exit_status = Some(i32::from(*status == Fail.sym()));
                    }
                    _ => {
                        vmprintln!(self.vm, "{}", e.to_string(&self.vm));
                    }
                }
            },
        }
    }

    pub fn exit_status(&self) -> Option<i32> {
        self.exit_status
    }

    pub fn print_intro(&mut self) {
        vmprint!(self.vm, "{}", make_intro());
    }

    #[cfg(not(feature = "readline"))]
    pub fn readline_repl(&mut self) -> ! {
        unimplemented!("readline not available")
    }

    #[cfg(feature = "readline")]
    pub fn readline_repl(&mut self) -> ! {
        let mut spaik_dir = dirs::data_local_dir().unwrap();
        spaik_dir.push("spaik");
        if let Err(e) = fs::create_dir_all(spaik_dir) {
            vmprintln!(self.vm, "Error: {}", e);
            process::exit(1);
        }
        let mut hist_path = dirs::data_local_dir().unwrap();
        hist_path.push("spaik");
        hist_path.push("history");
        let mut rl = Editor::<()>::new();
        if rl.load_history(&hist_path).is_err() {
            vmprintln!(self.vm, "{} {}",
                       "Warning: No history log, will be created in".style_warning(),
                       hist_path.to_string_lossy().style_info());
        }
        self.print_intro();
        let prompt = "λ> ".style_prompt().to_string();
        while self.exit_status.is_none() {
            let readline = rl.readline(&prompt);
            match readline {
                Ok(line) => {
                    rl.add_history_entry(line.as_str());
                    self.eval(line.as_str());
                },
                Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                    self.exit_status = Some(0)
                },
                Err(err) => {
                    vmprintln!(self.vm, "Read Error: {:?}", err);
                    self.exit_status = Some(1)
                }
            }
        }
        if let Err(e) = rl.save_history(&hist_path) {
            vmprintln!(self.vm, "Error: {}", e);
        }
        process::exit(self.exit_status.unwrap_or_default())
    }
}
