# Getting Started

To get started with Verus, use `git clone` to fetch the Verus source code from
the [Verus GitHub page](https://github.com/secure-foundations/verus),
and then follow the directions on
the [Verus GitHub page](https://github.com/secure-foundations/verus)
to build Verus.

Let's try running Verus on the following sample Rust program,
found at [getting_started.rs](https://github.com/secure-foundations/verus/tree/main/source/rust_verify/example/guide/getting_started.rs):

```rust
{{#include ../../../rust_verify/example/guide/getting_started.rs}}
```

To run Verus on this code, change to the `source` directory and type the following in Unix:

```
./tools/rust-verify.sh rust_verify/example/guide/getting_started.rs
```

or the following in Windows:

```
../rust/install/bin/rust_verify.exe --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/builtin_macros.dll --edition=2018 rust_verify/example/guide/getting_started.rs
```

You should see the following output:

```
note: verifying root module

verification results:: verified: 1 errors: 0
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
  --> rust_verify/example/guide/getting_started.rs:23:12
   |
23 |     assert(forall|i: int, j: int| min(i, j) == min(i, i));
   |            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed

error: aborting due to previous error

verification results:: verified: 0 errors: 1
```

## Using Verus in Rust files

Verus uses a macro named `verus!` to extend Rust's syntax with verification-related features
such as preconditions, postconditions, assertions, `forall`, `exists`, etc.
Therefore, each file in a crate will typically contain the following declarations:

```rust
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

verus! {
```

In the remainder of this guide, we will omit these declarations from the examples to avoid clutter.
However, remember that any example code should be placed inside the `verus! { ... }` block,
and that the file should use `builtin_macros::*;` and `builtin::*;`.

## Compilation

The instructions above verify a Rust file without compiling it.
To both verify and compile a Rust file, add the `--compile` command-line option.
For example:

```
./tools/rust-verify.sh --compile rust_verify/example/guide/getting_started.rs
```

This will generate an executable for `getting_started.rs`.
(However, in this example, the executable won't do anything interesting,
because the `main` function contains no executable code ---
it contains only statically-checked assertions,
which are erased before compilation.)
