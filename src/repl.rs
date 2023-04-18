//! Interactive Read-Eval-Print-Loop

#[cfg(feature = "readline")]
use rustyline::{Editor, error::ReadlineError};
#[cfg(feature = "readline")]
use std::{process, fs};
use crate::Spaik;
use crate::r8vm::OutStream;
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
    vm: Spaik,
    exit_status: Option<i32>,
}

impl REPL {
    pub fn new(out_override: Option<Box<dyn OutStream>>) -> REPL {
        let mut vm = Spaik::new();
        if let Some(out) = out_override {
            vm.vm.set_stdout(out);
        }
        REPL {
            vm,
            exit_status: None,
        }
    }

    pub fn eval(&mut self, code: impl AsRef<str>) -> Result<Option<String>, String> {
        let res = self.vm.vm.eval(code.as_ref());
        self.vm.vm.flush_output();
        match res {
            Ok(PV::Nil) => Ok(None),
            Ok(res) => Ok(Some(res.lisp_to_string(&self.vm.vm))),
            Err(e) => Err(e.to_string(&self.vm.vm)),
        }
    }

    pub fn exit_status(&self) -> Option<i32> {
        self.exit_status
    }

    pub fn print_intro(&mut self) {
        vmprint!(self.vm.vm, "{}", make_intro());
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
            vmprintln!(self.vm.vm, "Error: {}", e);
            process::exit(1);
        }
        let mut hist_path = dirs::data_local_dir().unwrap();
        hist_path.push("spaik");
        hist_path.push("history");
        self.vm.add_load_path(".");
        self.vm.add_load_path("lisp");
        let mut config_dir = dirs::config_dir().unwrap();
        config_dir.push("spaik");
        self.vm.add_load_path(config_dir.to_str().unwrap());
        match self.vm.load("init") {
            Ok(_) => (),
            Err(e) => {
                vmprintln!(self.vm.vm, "{}", e);
            }
        }
        let mut rl = Editor::<()>::new();
        if rl.load_history(&hist_path).is_err() {
            vmprintln!(self.vm.vm, "{} {}",
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
                    match self.eval(line.as_str()) {
                        Ok(Some(s)) => { vmprintln!(self.vm.vm, "{s}"); },
                        Err(e) => { vmprintln!(self.vm.vm, "{e}"); },
                        _ => ()
                    }
                },
                Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                    self.exit_status = Some(0)
                },
                Err(err) => {
                    vmprintln!(self.vm.vm, "Read Error: {:?}", err);
                    self.exit_status = Some(1)
                }
            }
        }
        if let Err(e) = rl.save_history(&hist_path) {
            vmprintln!(self.vm.vm, "Error: {}", e);
        }
        process::exit(self.exit_status.unwrap_or_default())
    }
}
