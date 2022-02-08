use std::process;

use spaik::repl::REPL;

fn main() {
    let mut repl = match REPL::new(None) {
        Err(e) => {
            println!("Error: {}", e);
            process::exit(1);
        }
        Ok(v) => v,
    };
    repl.readline_repl()
}
