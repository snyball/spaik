use clap::Parser;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
use tikv_jemallocator::Jemalloc;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use spaik::{run_tests, TestRunner, VmDebugOpts};
use std::process::exit;

#[derive(Debug, clap::Parser)]
pub struct Opts {
    #[command(flatten)]
    vm_dbg: VmDebugOpts,
}

fn main() {
    let opts = Opts::parse();
    let mut runner = TestRunner::new("./tests").unwrap();
    runner.set_debug(opts.vm_dbg);
    exit(match runner.run() {
        Ok(errs) if errs.len() == 0 => 0,
        Ok(_) => 1,
        Err(_) => 69
    })
}
