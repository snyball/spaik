use crate::r8vm::DevNull;
use crate::r8vm::R8VM;
use crate::OutStream;
use crate::VmDebugOpts;
use crate::VmStdout;
use crate::SPV;
use crate::Builtin;
use crate::stylize::Stylize;
use std::fmt;
use std::error::Error;
use std::fs;
use std::io;
use std::io::Write;
use std::path::Path;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Instant;

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

pub struct TestRunner {
    vm: R8VM,
}

impl TestRunner {
    pub fn new() -> crate::error::Result<Self> {
        let mut vm = R8VM::new();
        let buf: Box<dyn OutStream> = Box::new(DevNull);
        let outbuf = Arc::new(Mutex::new(buf));
        vm.set_stdout(outbuf.clone());
        let test = vm.sym_id("test");
        vm.eval(r#"(push sys/load-path "./lisp")"#).unwrap();
        vm.load_eval(test)?;
        Ok(Self {
            vm
        })
    }

    pub fn load(&mut self, file: impl AsRef<Path>) -> crate::error::Result<()> {
        self.vm.read_compile_from(file)?;
        Ok(())
    }

    pub fn load_all_from(&mut self, dir: impl AsRef<Path>) -> crate::error::Result<()> {
        let paths = fs::read_dir(dir)?.map(|p| p.map(|p| p.path()))
                                      .collect::<Result<Vec<_>, _>>()?;
        for path in paths {
            self.vm.read_compile_from(&path)?;
        }

        self.vm.minimize();

        Ok(())
    }

    pub fn set_debug(&mut self, dbg: VmDebugOpts) {
        self.vm.set_debug_mode(dbg);
    }

    pub fn run(mut self) -> crate::error::Result<Vec<TestError>> {
        let test_fn_prefix = "tests/";
        let test_fns = self.vm.get_funcs_with_prefix(test_fn_prefix);
        let mut err_results = vec![];

        let stdout = io::stdout();
        for func in test_fns.iter() {
            let name = func.as_ref()
                           .chars()
                           .skip(test_fn_prefix.len())
                           .collect::<String>();
            print!("test {} ... ", name.style_info());
            stdout.lock().flush().unwrap();
            let t0 = Instant::now();
            let r = self.vm.call_spv(*func, ());
            let t = Instant::now() - t0;
            match r {
                Ok(res) => match TestResult::new(res, &mut self.vm) {
                    Some(TestResult::Pass) => {
                        println!("{t:?} [{}]", "✓".style_success());
                    }
                    Some(TestResult::Fail { expect, got }) => {
                        let expect = expect.to_string(&self.vm.mem);
                        let got = got.to_string(&self.vm.mem);

                        println!("{t:?} [{}]", "✘".style_error());
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
                    println!("{t:?} [{}]", "✘".style_error());
                    for line in e.to_string().lines() {
                        println!("     {}", line);
                    }
                    err_results.push(TestError::RuntimeError { origin: e })
                },
            }
        }

        Ok(err_results)
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
    let mut runner = TestRunner::new()?;
    runner.load_all_from("./tests")?;
    let res = runner.run()?;
    Ok(res)
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
