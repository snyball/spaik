---
author: Jonas Møller
title: SPAIK
---

The **SPAIK** Lisp implementation:

plus.lisp

``` lisp
(defun plus (&rest xs)
  (let ((s 0))
    (dolist (x xs)
      (set s (+ s x)))
    s))
```

call.rs

``` rust
use spaik::spaik::Spaik;
use spaik::error::Error;

fn api_func_call() -> Result<(), Error> {
    let mut vm = Spaik::new()?;
    vm.load("plus")?;
    let (x, y, z) = (1, 2, 3);
    let result: i32 = vm.call("plus", (x, y, z, 4, 5))?;
    assert_eq!(result, 15);
}
```

The implementation includes the following main parts:

-   **CHASM**: generates virtual ISAs from a simple description of
    op-codes
-   **R8VM**: Stack-based virtual machine
    -   Supports tracebacks on errors
-   **NKGC**: Moving tri-color mark-compact garbage collector
-   **NUKE**: Allocation tools for the garbage collector
    -   These allocation utilities are written in C
-   **COMPILER**: Single-pass compiler and macro-expander.
-   **SINTERN**: String-interner
-   **ERROR**: Structural error type for gradually building errors
    upwards through the call stack.
-   **SPAIK**: Public API.

See `lisp/test.lisp` and the `tests/*.lisp` files for an example of a
non-trivial macro, and `lisp/self.lisp` for a non-trivial program.

# Usage of `unsafe`

This crate heavily utilizes `unsafe`, this is required for the following
operations:

## Accessing GC-memory directly

**SPAIK** uses a moving garbage-collector, meaning that pointers are not
necessarily valid after a call to `gc.collect()`, even if the pointer is
known to be part of the root set. External references to GC-allocated
memory need to use indirection (see `SPV` type,) but this indirection is
not used inside the VM and GC internals because of the overhead.

Instead, the VM and GC maintain the following invariant

> A `PV` value retrieved from the garbage collector arena may not be
> used after `gc.collect()` runs.

In practice this invariant is very easy to uphold in the internals. The
`unsafe` blocks themselves are sometimes hidden behind macros for
convenience.

``` rust
// An example of unsafe GC memory access, done ergonomically using a macro
with_ref_mut!(vec, Vector(v) => {
    let elem = v.pop().unwrap_or(PV::Nil);
    self.mem.push(elem);
    Ok(())
}).map_err(|e| e.op(Builtin::Pop.sym()))?;
```

## Accessing VM program memory

Program memory needs to be randomly accessed -- fast. But by default,
Rust will use bounds-checking on arrays. This bounds-checking is usually
cheap enough, but not for this particular use-case. The VM also only
supports relative jumps, which would have required two additions when
using indexing, but only one when using pointer arithmetic.

This optimization relies on:

-   The correctness of the compiled bytecode, i.e that the compiler does
    not produce out-of-bounds jumps.
-   On-the-fly changes to the bytecode may invalidate the pointer, so
    all operations that *may* result in program memory reallocation must
    reset the pointer.
    -   Return-pointers pushed onto the **SPAIK** call stack are
        indices, not raw pointers, for this reason.

## Converting between `u8` discriminants and `enum Thing`

**SPAIK** often needs to convert integer discriminants into enums, and
vice-versa. For this it uses `unsafe { mem::transmute(num) }`.
