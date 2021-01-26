use spaik::sexpr_parse::{tokenize, standard_lisp_tok_tree};
use std::env;
use std::ffi::OsStr;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

fn getext(filename: &str) -> Option<&str> {
    Path::new(filename).extension().and_then(OsStr::to_str)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut f = match &args[..] {
        [file] => File::open(file)?,
        _ => panic!("Invalid arguments: {:?}", args),
    };
    let mut code = String::new();
    f.read_to_string(&mut code)?;
    match getext(&args[0]) {
        Some("lisp") => {
            let tree = standard_lisp_tok_tree();
            tokenize(&code, &tree).unwrap();
        }
        Some(x) => panic!("Unknown file extension: {}", x),
        None => panic!("No file extension"),
    };

    Ok(())
}
