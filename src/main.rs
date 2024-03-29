#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
use jemallocator::Jemalloc;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;
use spaik::Spaik;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::io;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut f: Box<dyn Read> = match &args[..] {
        [file] => Box::new(File::open(file)?),
        [] => Box::new(io::stdin()),
        _ => panic!("Invalid arguments: {:?}", args),
    };
    let mut code = String::new();
    if f.read_to_string(&mut code).is_err() {
        return Ok(())
    }
    let mut vm = Spaik::new_no_core();
    match vm.exec(&code) {
        Ok(_) => (),
        Err(e) => eprintln!("{}", e),
    }
    vm.trace_report();

    Ok(())
}
