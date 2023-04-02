use iai::{black_box, main};
use spaik::run_tests;

fn run_lisp_tests() {
    run_tests().unwrap();
}

iai::main!(run_lisp_tests);
