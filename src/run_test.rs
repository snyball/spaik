use spaik::r8vm::*;

fn main() {
    let mut vm = R8VM::new();
    vm.read("(println (list 1 2 3 4 5 6))").unwrap();
    let sym = vm.compile("test");
    vm.dis();
    let args = vec![];
    vm.call(sym, args).unwrap();
}
