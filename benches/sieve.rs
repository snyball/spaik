use iai::black_box;
use spaik::Spaik;

fn run_sieve() {
    let sieve_lisp = include_str!("sieve.lisp");
    let mut vm = Spaik::new();
    black_box(vm.exec(black_box(sieve_lisp)).unwrap());
}

iai::main!(run_sieve);
