# Getting started on the command line

## 1. Install Verus.

To install Verus, follow the instructions at [INSTALL.md](https://github.com/verus-lang/verus/blob/main/INSTALL.md).

## 2. Verify a sample program.

Create a file called `getting_started.rs`, and paste in the following contents:

```rust
{{#include ../../../../examples/guide/getting_started.rs}}
```

To run Verus on the file:

If on macOS, Linux, or similar system, run:

```
/path/to/verus getting_started.rs
```

If on Windows, run:

```
.\path\to\verus.exe getting_started.rs
```

You should see the following output:

```
note: verifying root module

verification results:: 1 verified, 0 errors
```

This indicates that Verus successfully verified 1 function (the `main` function).

### Try it on code that won't verify

If you want, you can try editing the `getting_started.rs` file
to see a verification failure.
For example, if you add the following line to `main`:

```
    assert(forall|i: int, j: int| min(i, j) == min(i, i));
```

you will see an error message:

```
note: verifying root module

error: assertion failed
  --> getting_started.rs:19:12
   |
19 |     assert(forall|i: int, j: int| min(i, j) == min(i, i));
   |            ^^^^^^ assertion failed

error: aborting due to previous error

verification results:: 0 verified, 1 errors
```

## 3. Compile the program

The command above only verifies the code, but does not compile it. If you also want to compile
it to a binary, you can `verus` with the `--compile` flag.

If on macOS, Linux, or similar system, run:

```
/path/to/verus getting_started.rs --compile
```

If on Windows, run:

```
.\path\to\verus.exe getting_started.rs --compile
```

Either will create a binary `getting_started`.

However, in this example, the binary won't do anything interesting
because the `main` function contains no executable code ---
it contains only statically-checked assertions,
which are erased before compilation.

## 4. Learn more about Verus

[Continue with the tutorial](./verus_macro_intro.md), starting with an explanation of the `verus!` macro from the above example.
