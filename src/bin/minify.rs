use std::{fs, env::args, io::stdout, process::exit};

fn usage() -> ! {
    println!("Usage: minify <file>");
    exit(1);
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut argv = args();
    let Some(_) = argv.next() else { usage() };
    let Some(arg) = argv.next() else { usage() };
    let code = fs::read_to_string(arg)?;
    spaik::minify(&code, &mut stdout().lock())?;
    Ok(())
}
