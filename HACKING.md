# Hacking SPAIK

### Important internal types

- `PV` Primitive Value
- `*mut NkAtom` Atom Pointer

`PV` is the Lisp primitive value, it can be a float, integer, symbol, etc. or
it can refer to GC memory via a `PV::Ref(*mut NkAtom)` pointer. Interacting with
a `PV` is always `unsafe`, and occasionally highly precarious. SPAIK uses a
moving garbage collector, which means that even if the referenced memory is a
part of the [root set][1] a garbage collection cycle could invalidate the pointer.
In practice, you have to maintain the following invariant:

> A `PV` value taken from the SPAIK root-set cannot be dereferenced after
> `Arena::collect` runs.

[1]: https://en.wikipedia.org/wiki/Tracing_garbage_collection

So if you acquire a `PV`, that value is valid until some manner of `eval`
happens, because any evaluation of code can cause a garbage collection sweep.

### Interacting with primitive values

In order to ergonomically dereference a `PV`, you can make use of the `with_ref!` and `with_ref_mut!` macros.

```rust
let it = self.mem.pop()?;
with_ref!(it, Cons(p) => {
    self.mem.push((*p).car);
    Ok(())
}).map_err(|e| e.bop(Builtin::Car))?
```

The `with_ref!` macro typechecks and constructs appropriate error messages.

> Type Error: Expected one of (cons) in car, but got integer [x.lisp 408:3]

Note: Information about what operation was performed (in this case car,) is
added with the `e.bop(Builtin::Op)` call (bop, for built-in-operation.)

### What if I need to keep a PV around?

There are 3 main options:

1. Just keep it in the VM, and never store it permanently somewhere on the Rust
   stack/heap.
2. Use `SPV`, call `Arena::make_extref(pv)` and receive a Safe Primitive Value,
   a thread-safe way to refer to a SPAIK GC object.
   - `SpaikPlug` uses this to implement async/await.
3. If performance is a concern, you can push/pop the value to/from the VM stack.
   Whenever you do anything that leads to eval do `vm.mem.push(pv)` and then
   `pv = vm.mem.pop().unwrap()` after evaluation finishes.
   - Some of the hairiest bits of the VM, like `R8VM::macroexpand_pv` are
     examples of this approach.
   - SPAIK uses the convention `invalid!(x, y, z) // <function that made them invalid>` for marking variables that become invalidated.
     - **Do not rely on all invalidated variables being documented**

### NkAtom layout

An `NkAtom` looks like this:

```rust
#[repr(C)]
pub struct NkAtom {
    next: *mut NkAtom,
    sz: NkSz,
    meta: AtomMeta,
}
```

Following `next` leads to the next object in the GC memory, `sz` is the size of
the allocated object, and `meta` holds the type and [color][2] of the object.

[2]: https://en.wikipedia.org/wiki/Tracing_garbage_collection#Tri-color_marking

Strangely missing however is the object itself, which is actually stored
directly after the `NkAtom`. The definition neglects to mention that, because
there is no safe way to express a "`dyn` DST" in Rust. This is how we can turn
an `NkAtom` into the `T` it contains

```rust
pub unsafe fn fastcast_mut<T>(atom: *mut NkAtom) -> *mut T {
    const DELTA: isize = mem::size_of::<NkAtom>() as isize;
    let p = (atom as *mut u8).offset(DELTA);
    align_mut(p, align_of::<T>() as isize) as *mut T
}
```

When an object is allocated in the SPAIK GC, it gets allocated with an `NkAtom`
header followed by any padding, and then the object itself.

However `fastcast_mut` is essentially just as unsafe as `mem::transmute`, in
order to do this safely we use the wrapper `cast_mut`:

```rust
pub unsafe fn cast_mut<T: Fissile>(atom: *mut NkAtom) -> Option<*mut T> {
    let ty = T::type_of();
    let got = mem::transmute((*atom).meta.typ());
    (ty == got).then(|| fastcast_mut::<T>(atom))
}
```

The `Fissile` trait is a marker for any objects that can be stored directly in
the SPAIK GC, it looks like this:

```rust
pub unsafe trait Fissile: LispFmt + Debug + Clone + Traceable + Any + 'static {
    fn type_of() -> NkT;
}
```

Adding a new internal type to SPAIK means making it Fissile, by putting it in
the `fissile_types!` invocation in `nuke.rs`.

```rust
fissile_types! {
    (/* Given name */ Void, /* Symbol */ Builtin::Void.sym(), /* Type */ crate::nuke::Void),
    // ...
}
```

If you would like to dereference a `PV` without `with_ref!`, this is what
`with_ref!` does internally:

```rust
match pv {
    PV::Ref(p) => match to_fissile_ref(p) {
        NkRef::Cons(p) => {
            println!("pointer to Cons: {p:?}")
        }
        NkRef::Vector(p) => {
            println!("pointer to Vec<PV>: {p:?}")
        }
        _ => Err(...)
    }
    _ => Err(...)
}
```
