//! Interactive Read-Eval-Print-Loop

use rustyline::error::ReadlineError;
use rustyline::Editor;
use spaik::r8vm::R8VM;
use spaik::nkgc::PV;
use spaik::compile::Builtin;
use spaik::error::{Error, ErrorKind};
use spaik::fmt::LispFmt;
use std::process;
use std::fs;
use colored::*;

fn make_intro() -> String {
    format!("
{read} {arrow} {eval} {arrow} {print} {arrow} {loop}
 ┗━━━━━━━━━━━━━━━━━━━━━━┛\n",
            read="read".blue().bold().underline(),
            eval="eval".blue().bold().underline(),
            print="print".blue().bold().underline(),
            loop="loop".blue().bold().underline(),
            arrow="➟"
    )
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let intro =
"
read ➟ eval ➟ print ➟ loop
 ┗━━━━━━━━━━━━━━━━━━━━━━┛
";
    // println!("{}", intro.white().bold());
    println!("{}", make_intro());
    let mut vm = R8VM::new();
    let mut spaik_dir = dirs::data_local_dir().unwrap();
    spaik_dir.push("spaik");
    fs::create_dir_all(spaik_dir)?;
    let mut hist_path = dirs::data_local_dir().unwrap();
    hist_path.push("spaik");
    hist_path.push("history");
    let mut rl = Editor::<()>::new();
    if rl.load_history(&hist_path).is_err() {
        println!("{} {}",
                 "Warning: No history log, will be created in".yellow().bold(),
                 hist_path.to_string_lossy().white().bold());
    }
    let stdlib = vm.sym_id("stdlib");
    if let Err(e) = vm.load(stdlib) {
        println!("{}", e.to_string(&vm));
        process::exit(1);
    }
    loop {
        let readline = rl.readline(&"λ> ".white().bold().to_string());
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                match vm.eval(line.as_str()) {
                    Ok(PV::Nil) => {}
                    Ok(res) => {
                        print!("{}", "=> ".blue().bold());
                        println!("{}", res.lisp_to_string(&vm))
                    },
                    Err(e) => {
                        match e.cause() {
                            Error { ty: ErrorKind::Exit { status }, ..} => {
                                use Builtin::*;
                                rl.save_history(&hist_path)?;
                                if *status == Fail.sym() {
                                    process::exit(1);
                                }
                                process::exit(0);
                            }
                            _ => {
                                println!("{}", e.to_string(&vm))
                            }
                        }
                    },
                }
            },
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                break
            },
            Err(err) => {
                println!("Read Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history(&hist_path)?;
    Ok(())
}
