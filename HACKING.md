# Hacking SPAIK

### Important internal types

- `PV` Primitive Value
- `*mut NkAtom` Nuclear Atom Pointer

A `PV` is the Lisp primitive value, it can be a float, integer, symbol, etc. or
it can refer to GC memory via a `PV::Ref(*mut NkAtom)` pointer. Interacting with
a `PV` is always `unsafe`, and occasionally highly precarious. SPAIK uses a
moving garbage collector, which means that even if the referenced memory is a
part of the [root set][1] a garbage collection cycle could invalidate the pointer.
In practice, you have to maintain the following invariant:

> A `PV` value taken from the SPAIK root-set cannot be dereferenced after
> `Arena::collect` runs.

[1]: https://en.wikipedia.org/wiki/Tracing_garbage_collection

So if you acquire a `PV`, that value is valid until some manner of `eval`
happens, which could potentially lead to `Arena::sweep_compact`.

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
