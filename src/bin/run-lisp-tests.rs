use clap::Parser;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
use tikv_jemallocator::Jemalloc;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use spaik::{TestRunner, VmDebugOpts};
use std::{path::PathBuf, process::exit};

#[derive(Debug, clap::Parser)]
pub struct Opts {
    #[command(flatten)]
    pub vm_dbg: VmDebugOpts,
    #[cfg_attr(feature = "cli", arg(long))]
    pub only_load: bool,
    pub files: Vec<PathBuf>,
}

fn main() {
    pretty_env_logger::init();
    let opts = Opts::parse();
    let mut runner = TestRunner::new().unwrap();
    if opts.files.is_empty() {
        runner.load_all_from("./tests").unwrap();
    } else {
        for path in opts.files.iter() {
            runner.load(path).unwrap();
        }
    }
    if opts.only_load {
        return;
    }
    runner.set_debug(opts.vm_dbg);
    exit(match runner.run() {
        Ok(errs) if errs.len() == 0 => 0,
        Ok(_) => 1,
        Err(_) => 69
    })
}
