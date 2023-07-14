# Getting Started

To get started with Verus, use `git clone` to fetch the Verus source code from
the [Verus GitHub page](https://github.com/verus-lang/verus),
and then follow the directions on
the [Verus GitHub page](https://github.com/verus-lang/verus/blob/main/INSTALL.md)
to build Verus.

Let's try running Verus on the following sample Rust program,
found at [getting_started.rs](https://github.com/verus-lang/verus/tree/main/source/rust_verify/example/guide/getting_started.rs):

```rust
{{#include ../../../rust_verify/example/guide/getting_started.rs}}
```

To run Verus on this code, change to the `source` directory and type the following in Unix:

```
./target-verus/release/verus rust_verify/example/guide/getting_started.rs
```

or the following in Windows:

```
.\target-verus\release\verus.exe rust_verify\example\guide\getting_started.rs
```

You should see the following output:

```
note: verifying root module

verification results:: 1 verified, 0 errors
```

This indicates that Verus successfully verified 1 function (the `main` function).
If you want, you can try editing the `rust_verify/example/guide/getting_started.rs` file
to see a verification failure.
For example, if you add the following line to `main`:

```
    assert(forall|i: int, j: int| min(i, j) == min(i, i));
```

you will see an error message:

```
note: verifying root module

error: assertion failed
  --> example/guide/getting_started.rs:19:12
   |
19 |     assert(forall|i: int, j: int| min(i, j) == min(i, i));
   |            ^^^^^^ assertion failed

error: aborting due to previous error

verification results:: 0 verified, 1 errors
```

## Using Verus in Rust files

Verus uses a macro named `verus!` to extend Rust's syntax with verification-related features
such as preconditions, postconditions, assertions, `forall`, `exists`, etc.
Therefore, each file in a crate will typically contain the following declarations:

```rust
use vstd::prelude::*;

verus! {
```

In the remainder of this guide, we will omit these declarations from the examples to avoid clutter.
However, remember that any example code should be placed inside the `verus! { ... }` block,
and that the file should use `vstd::prelude::*;`.

## Compilation

The instructions above verify a Rust file without compiling it.
To both verify and compile a Rust file, add the `--compile` command-line option.
For example:

```
./target-verus/release/verus --compile rust_verify/example/guide/getting_started.rs
```

This will generate an executable for `getting_started.rs`.
(However, in this example, the executable won't do anything interesting,
because the `main` function contains no executable code ---
it contains only statically-checked assertions,
which are erased before compilation.)
