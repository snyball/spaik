extern crate bindgen;

use std::env;
use std::path::PathBuf;

fn main() {
    let lib_h = "src/nuke.h";
    let lib_c = "src/nuke.c";

    // Tell cargo to invalidate the built crate whenever the wrapper changes
    println!("cargo:rerun-if-changed={}", lib_h);
    println!("cargo:rerun-if-changed={}", lib_c);
    let bindings = bindgen::Builder::default()
        .header(lib_h)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    cc::Build::new()
        .file(lib_c)
        .define("DEBUG", Some("0"))
        //.opt_level_str("fast")
        .flag("-Wall")
        .flag("-pedantic")
        .flag("-Werror")
        .include("src")
        .compile("nuke");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings.write_to_file(out_path.join("nuke-sys.rs"))
            .expect("Couldn't write bindings!");
}
