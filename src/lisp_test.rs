use spaik::r8vm::R8VM;
use spaik::nkgc::SPV;
use spaik::compile::Builtin;
use colored::*;
use std::{fs, fmt};
use std::fs::File;
use std::io::prelude::*;
use std::error::Error;
use std::process::exit;

enum TestResult {
    Pass,
    Fail {
        expect: SPV,
        got: SPV
    }
}

impl TestResult {
    pub fn new(res: SPV) -> Option<TestResult> {
        Some(match res.bt_op() {
            Some(Builtin::KwPass) => TestResult::Pass,
            Some(Builtin::KwFail) => {
                let args = res.args().collect::<Vec<_>>();
                match &args[..] {
                    [expect, got] => TestResult::Fail { expect: expect.clone(),
                                                        got: got.clone() },
                    _ => return None
                }
            }
            _ => return None
        })
    }
}

#[derive(Debug)]
enum TestError {
    WrongResult {
        expect: String,
        got: String,
    },
    RuntimeError {
        origin: spaik::error::Error,
    }
}

impl fmt::Display for TestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            TestError::RuntimeError { origin } => write!(f, "{origin}"),
            TestError::WrongResult { expect, got } => {
                write!(f, "{expect} != {got}")
            }
        }
    }
}

impl Error for TestError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TestError::RuntimeError { origin } => Some(origin),
            _ => None
        }
    }

    fn cause(&self) -> Option<&dyn Error> {
        self.source()
    }
}

fn run_tests() -> Result<Vec<TestError>, Box<dyn Error>> {
    let mut vm = R8VM::new();
    let tests_path = "./tests";
    let stdlib = vm.sym_id("stdlib");
    let test = vm.sym_id("test");

    match vm.load(stdlib).and_then(|_| vm.load(test)) {
        Err(e) => {
            println!("{}", e.to_string(&vm));
            return Err(e.into());
        }
        _ => ()
    }

    let paths = fs::read_dir(tests_path)?.map(|p| p.map(|p| p.path()))
                                         .collect::<Result<Vec<_>, _>>()?;
    for path in paths {
        let mut file = File::open(&path)?;
        let mut test_src = String::new();
        file.read_to_string(&mut test_src)?;
        match vm.eval(&test_src) {
            Ok(_) => println!("Loaded {}", path.display()),
            Err(e) => {
                println!("Error when loading {}", path.display());
                println!("{}", e.to_string(&vm));
                return Err(e.into());
            },
        }
    }

    vm.minimize();

    let test_fn_prefix = "tests/";
    let test_fns = vm.get_funcs_with_prefix(test_fn_prefix);
    let mut err_results = vec![];

    println!("Running tests ...");
    for func in test_fns.iter() {
        let name = vm.sym_name(*func)
                     .chars()
                     .skip(test_fn_prefix.len())
                     .collect::<String>();
        match vm.call_spv(*func, ()) {
            Ok(res) => match TestResult::new(res) {
                Some(TestResult::Pass) =>
                    println!("  - {} [{}]", name.bold(), "✓".green().bold()),
                Some(TestResult::Fail { expect, got }) => {
                    let expect = expect.to_string();
                    let got = got.to_string();

                    println!("  - {} [{}]", name.red().bold(), "✘".red().bold());
                    println!("    Expected:");
                    for line in expect.lines() {
                        println!("      {}", line);
                    }
                    println!("    Got:");
                    for line in got.to_string().lines() {
                        println!("      {}", line);
                    }

                    err_results.push(TestError::WrongResult { expect, got });
                }
                _ => ()
            }
            Err(e) => {
                println!("  - {} [{}]", name.red().bold(), "✘".red().bold());
                for line in e.to_string(&vm).lines() {
                    println!("    {}", line)
                }
                err_results.push(TestError::RuntimeError { origin: e })
            },
        }
    }

    Ok(err_results)
}

fn main() {
    exit(match run_tests() {
        Ok(_) => 0,
        Err(_) => 1
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lisp_tests() {
        let results = run_tests().unwrap();
        for res in results {
            panic!("{res}");
        }
    }
}
