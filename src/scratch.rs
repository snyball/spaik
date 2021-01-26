#[allow(unused_imports)]
use risp::parse::*;
#[allow(unused_imports)]
use risp::data::*;
#[allow(unused_imports)]
use risp::r8vm::*;
#[allow(unused_imports)]
use risp::nkgc::*;
#[allow(unused_imports)]
use risp::nuke::*;
#[allow(unused_imports)]
use risp::nk::*;
#[allow(unused_imports)]
use regex::*;

// Rust doesn't have a REPL, this is my substitute.

fn main() {
    let rx: Regex = Regex::new(r#"(?xm)
        (?P<cmnt> ;.*$)
        |
        (?P<str> r?"( \\" | [^"] )*")
        |
        (?P<strerr> ")
        |
        (?P<op> ( [\^]
                | '
                | `
                | \|
                | \$
                | \#
                | ,@
                | ,
                | ¬
                ) )
        |
        (?P<real> [+-]?\d+\.\d+(e\d+)?\b)
        |
        (?P<int> [+-]?\d+\b)
        |
        (?P<sym> [:_/?!&~\*+=%<>\d\w-]+)
        |
        (?P<delim> ( \(|\)
                    | \[|\]
                    | \{|\}
                    ) )
        |
        (?P<invalid> \S+)
    "#).unwrap();
    // let vm = R8VM::new();
    // let func = sym!(YES);
    // let res = vm.rips!(func 1 2 3)?;
    // let res = rp!{ vm:"kebab-function"(1, 2, 3) }?;
    rx.find("yes");
}
