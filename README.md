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
assert_eq!(vm.eval("(f 2)"), Ok(4));

// Optional linear-algebra types from glam
vm.exec("(defun funky (x y) (* x (vec3 1 y 3)))")?;
assert_eq!(vm.call("funky", (2, 4)), Ok(glam::vec3(2.0, 8.0, 6.0))); // Call a spaik function

// Define interfaces more formally
defuns!(trait MyInterface {
    fn funky(x: f32, y: f32) -> glam::Vec3;
});
// This panics if the function `funky` does not match the spec
assert_eq!(vm.funky(2.0, 4.0), glam::vec3(2.0, 8.0, 6.0));
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

### Events/hooks

SPAIK comes with a convenient mechanism for defining and calling hooks.

```common-lisp
(defun event/ready ()
  (message "Is ready!"))
```

```rust
#[spaik::hooks("event/")]
trait ScriptEvents {
    fn ready();
    fn timer(id: u32);
    fn tick(ticks: u32);
}

pub fn main() -> Result<(), E> {
    let mut vm = Self::new_vm();
    vm.load("thing")?;
    let mut hooks = ScriptEvents::default();
    hooks.link_events(&mut vm);
    hooks.on(&mut self.vm)
         .catch_all()
         .ready(); // Calls `event/ready` in the VM
    Ok(())
}
```

### Continuations

Continuations are implemented using `call/cc`, here's an example using them
to implement sleeping.

```common-lisp
(define *timer-tbl* (make-table))

(defun event/timer (id)
  (let ((k (get *timer-tbl* id)))
    (del *timer-tbl* id)
    ;; Here the continuation is called
    (k nil)))

(defun sleep (seconds)
  ;; Save our continuation in the global table, then exit to Rust by throwing
  (call/cc (lambda (k)
             (set (get *timer-tbl* (timers/add seconds)) k)
             (throw 'async-sleep nil))))

(defun event/something-happened ()
  (message "Wait for it...")
  (sleep 2)
  (message "Surprise!))
```

In this case you're responsible for implementing the `(timers/add <seconds>)`
function and a system for calling `(event/timer <id>)` when the timers fire.

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
