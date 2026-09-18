use clap::Parser;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
use tikv_jemallocator::Jemalloc;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;
use spaik::{Spaik, VmDebugOpts};
use std::io::prelude::*;
use std::io;
use std::path::PathBuf;

#[derive(Debug, clap::Parser)]
pub struct Opts {
    file: Option<PathBuf>,
    #[command(flatten)]
    vm_dbg: VmDebugOpts,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(feature = "pretty_env_logger")]
    pretty_env_logger::init();
    let opts = Opts::parse();
    let mut vm = Spaik::new();
    vm.set_debug(opts.vm_dbg);
    let r = if let Some(path) = opts.file {
        vm.exec_from_path(path)
    } else {
        let mut code = String::new();
        io::stdin().read_to_string(&mut code)?;
        vm.exec(code)
    };
    match r {
        Ok(_) => (),
        Err(e) => eprintln!("{}", e),
    }
    vm.trace_report();
    vm.log_stats();

    Ok(())
}
