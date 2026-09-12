#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
use tikv_jemallocator::Jemalloc;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use spaik::run_tests;
use std::process::exit;

fn main() {
    exit(match run_tests() {
        Ok(errs) if errs.len() == 0 => 0,
        Ok(_) => 1,
        Err(_) => 69
    })
}
