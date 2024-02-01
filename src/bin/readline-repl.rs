use spaik::repl::REPL;

fn main() {
    pretty_env_logger::init();
    let mut repl = REPL::new(None);
    repl.readline_repl()
}
