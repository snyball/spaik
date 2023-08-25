The SPAIK LISP Programming Language
===================================

SPAIK is a dynamic extension language for Rust. It implements macros, garbage
collection, iterators, continuations, async/await and wraps it up in a
(hopefully) easy to use high-level Rust API.

This README contains many shorts snippets showing how SPAIK is used, while you
can find complete examples in the [examples](examples) directory, and the more
detailed API docs can be found at [docs.rs](https://docs.rs/spaik/latest/spaik/).

[You can also try SPAIK directly in your
browser!](https://snyball.github.io/spaik-site/)

### Basic usage

For basic usage, all you need are the `eval` and `exec` methods (`exec` is just
`eval` but it throws away the result to aid type-inference.)

``` rust
let mut vm = Spaik::new();
vm.exec(r#"(println "Hello, World!")"#)?;

vm.set("f", |x: i32| x + 2); // Functions are first-class at the API boundary!
assert_eq!(vm.eval("(f 2)")?, 4)
```

### Loading Code

You probably don't want to store all your SPAIK code as embedded strings in Rust,
so you can of course load SPAIK scripts from the filesystem.

``` rust
vm.add_load_path("my-spaik-programs");
vm.load::<Ignore>("stuff")?;
let result: Lambda = vm.load("other-stuff")?;
result.call(&mut vm, (1, 2, 3));
```

The `add_load_path` method adds the given string to the global `sys/load-path`
variable, which is just a SPAIK vector. You can mutate this from SPAIK too:

``` common-lisp
(eval-when-compile (push sys/load-path "my-dependencies"))
(load dependency)
```

But notice that we had to use `(eval-when-compile ...)` when adding the new
path, because `(load ...)` also runs during compilation.

### Exporting functions to SPAIK

You can simply `vm.set("name", func)`, or use the convenience-function
`vm.defun(add_to)`, which is equivalent to `vm.set("add-to", add_to)`.

``` rust
use spaik::prelude::*;

fn add_to(x: i32) -> i32 {
    x + 1
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();
    println!("Calling from Rust: {}", add_to(2));
    vm.set("other-name-for-add-to", add_to);
    vm.defun(add_to);
    vm.exec(r#"(let ((r (add-to 2))) (println "Calling Rust from SPAIK: {r}"))"#)?;
    Ok(())
}
```

### The `html` macro

Because of how easy it is to create new syntax constructs in LISPs, you can
use SPAIK as a rudimentary html templating engine.

``` common-lisp
(load html)
(html (p :class 'interjection "Interjection!"))
```

``` html
<p class="interjection">Interjection!</p>
```


### Internal Architecture

SPAIK code is bytecode compiled and runs on a custom VM called the Rodent VM
(R8VM,) which uses a moving tracing garbage collector. For more detailed
information about its internals, see [HACKING.md](HACKING.md).
