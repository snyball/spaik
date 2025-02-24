use spaik::run_tests;
use std::process::exit;

fn main() {
    exit(match run_tests() {
        Ok(_) => 0,
        Err(_) => 1
    })
}
