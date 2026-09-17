use crate::r8vm::DevNull;
use crate::r8vm::R8VM;
use crate::OutStream;
use crate::VmStdout;
use crate::SPV;
use crate::Builtin;
use crate::stylize::Stylize;
use std::fmt;
use std::error::Error;
use std::fs;
use std::sync::Arc;
use std::sync::Mutex;

enum TestResult {
    Pass,
    Fail {
        expect: SPV,
        got: SPV
    }
}

impl TestResult {
    pub fn new(res: SPV, vm: &mut R8VM) -> Option<TestResult> {
        Some(match res.bt_op(&vm.mem) {
            Some(Builtin::KwPass) => TestResult::Pass,
            Some(Builtin::KwFail) => {
                let args = res.args_vec(&mut vm.mem);
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
pub enum TestError {
    WrongResult {
        expect: String,
        got: String,
    },
    RuntimeError {
        origin: crate::error::Error,
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

/// Run SPAIK tests from the `./tests` directory and report any errors.
pub fn run_tests() -> Result<Vec<TestError>, Box<dyn Error>> {
    #[cfg(feature = "pretty_env_logger")]
    pretty_env_logger::init();
    let mut vm = R8VM::new();
    let buf: Box<dyn OutStream> = Box::new(DevNull);
    let outbuf = Arc::new(Mutex::new(buf));
    vm.set_stdout(outbuf.clone());
    let tests_path = "./tests";
    let test = vm.sym_id("test");
    vm.eval(r#"(push sys/load-path "./lisp")"#).unwrap();

    if let Err(e) = vm.load_eval(test) {
        println!("{e}");
        return Err(e.into());
    }

    let paths = fs::read_dir(tests_path)?.map(|p| p.map(|p| p.path()))
                                         .collect::<Result<Vec<_>, _>>()?;
    for path in paths {
        match vm.read_compile_from(&path) {
            Ok(_) => (),
            Err(e) => {
                println!("Error when loading {}", path.display());
                println!("{e}");
                return Err(e.to_string().into());
            },
        }
    }

    vm.minimize();

    let test_fn_prefix = "tests/";
    let test_fns = vm.get_funcs_with_prefix(test_fn_prefix);
    let mut err_results = vec![];

    for func in test_fns.iter() {
        let name = func.as_ref()
                       .chars()
                       .skip(test_fn_prefix.len())
                       .collect::<String>();
        match vm.call_spv(*func, ()) {
            Ok(res) => match TestResult::new(res, &mut vm) {
                Some(TestResult::Pass) => {
                    println!("test {} ... [{}]",
                        name.style_info(),
                        "✓".style_success());
                }
                Some(TestResult::Fail { expect, got }) => {
                    let expect = expect.to_string(&vm.mem);
                    let got = got.to_string(&vm.mem);

                    println!("test {} ... [{}]",
                        name.style_error(),
                        "✘".style_error());
                    println!("     Expected:");
                    for line in expect.lines() {
                        println!("       {}", line);
                    }
                    println!("     Got:");
                    for line in got.to_string().lines() {
                        println!("       {}", line)
                    }

                    err_results.push(TestError::WrongResult { expect, got });
                }
                _ => ()
            }
            Err(e) => {
                println!("test {} [{}]",
                    name.style_error(),
                    "✘".style_error());
                for line in e.to_string().lines() {
                    println!("     {}", line);
                }
                err_results.push(TestError::RuntimeError { origin: e })
            },
        }
    }

    Ok(err_results)
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
