The SPAIK LISP Programming Language
===================================

SPAIK is a dynamic extension language for Rust. It implements macros, garbage
collection, iterators, continuations, async/await and wraps it up in a
(hopefully) easy to use high-level Rust API.

### Basic usage

For basic usage, all you need are the `eval` and `exec` methods, `exec` is
just `eval` but it throws away the result.

``` rust
let mut vm = Spaik::new();
vm.exec(r#"(println "Hello, World!")"#)?;
vm.set("*global*", 3);
let res: i32 = vm.eval(r#"(+ 1 *global*)"#)?;
assert_eq!(res, 4);
// Equivalent to exec
let _: Ignore = vm.eval(r#"(+ 1 *global*)"#)?;
```

### Exporting functions to SPAIK

It is often useful to for functions to be called from both Rust and Lisp,
here the function `add_to` is being defined as both a Rust function in the
global scope, and as a SPAIK function in `Fns`. We can then choose to 
register the `Fns::add_to` function in the VM.

``` rust
use spaik::prelude::*;

struct Fns;

#[spaikfn(Fns)]
fn add_to(x: i32) -> i32 {
    x + 1
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();
    println!("Calling from Rust: {}", add_to(2));
    vm.register(Fns::add_to);
    vm.exec(r#"(let ((r (add-to 2))) (println "Calling Rust from SPAIK: {r}"))"#)?;
    Ok(())
}
```

### Command pattern, or "call-by-enum"

One ergonomic way to interact with a dynamic PL VM from Rust is to use the
command pattern, which you can think of as "call-by-enum." The full example
can be found in [examples/command-pattern-multi-threaded](examples/command-pattern-multi-threaded)

``` rust
enum Cmd {
    Add(i32),
    Subtract(i32),
}

// We can fork the vm onto its own thread first
let mut vm = vm.fork::<Msg, Cmd>();

vm.cmd(Cmd::Add(1337));
vm.cmd(Cmd::Add(31337));

// Loop until all commands have been responded to
while recvd < 2 {
    processing();
    while let Some(p) = vm.recv() {
        vm.fulfil(p, 31337);
        recvd += 1;
    }
}

// Join with the VM on the same thread again
let mut vm = vm.join();
let glob: i32 = vm.eval("*global*").unwrap();
```

``` common-lisp
(define *global* 0)

(defun init ())

(defun add (x)
  (let ((res (await '(test :id 1337))))
    (set *global* (+ *global* res x 1))))
```

When using call-by-enum in a single-threaded setup, use the `query` method
instead, which immediately returns the result. The `cmd` function also exists
for single-threaded `Spaik`, but returns `Result<()>`.

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



