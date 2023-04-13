use spaik::repl::REPL;

fn main() {
    let mut repl = REPL::new(None);
    repl.readline_repl()
}
