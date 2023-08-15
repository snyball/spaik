use spaik::prelude::*;

struct Fns;

fn add_to(x: i32) -> i32 {
    x + 1
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();
    println!("Calling from Rust: {}", add_to(2));
    vm.set("add-to", add_to);
    vm.exec(r#"(let ((r (add-to 2))) (println "Calling Rust from SPAIK: {r}"))"#)?;
    Ok(())
}
