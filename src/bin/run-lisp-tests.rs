#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
use jemallocator::Jemalloc;
#[cfg(all(target_env = "musl", target_pointer_width = "64"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use spaik::run_tests;
use std::process::exit;

fn main() {
    exit(match run_tests() {
        Ok(_) => 0,
        Err(_) => 1
    })
}
