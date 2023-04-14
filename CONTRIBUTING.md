# Tips for Contributing to Verus

Thanks for contributing to Verus!  Verus is an Open Source project and welcomes
contributions.  Please report issues or start discussions here on GitHub.

We use GitHub discussions for feature requests and more open-ended conversations about
upcoming features, and we reserve GitHub issues for actionable issues (bugs) with
existing features. Don't worry though: if we think an issue should be a discussion (or
viceversa) we can always move it later.

## Editing the Source Code of Verus

Before committing any changes to the source code,
make sure that it conforms to the `rustfmt` tool's guidelines.
We are using the default `rustfmt` settings from the Rust repository.
To check the source code, type the following from the `source` directory:

```
vargo fmt -- --check
```

If the source code follows the guidelines, `vargo fmt -- --check` will produce no output.
Otherwise, it will report suggestions on how to reformat the source code.

To automatically apply these suggestions to the source code, type:

```
vargo fmt
```

## Code Documentation

Commenting the code is strongly encouraged.  Use `///` to create comments
that [`rustdoc`](https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html) can
automatically extract into HTML documentation.

The rustdoc (verusdoc) for `main` is automatically published
[📖 here](https://verus-lang.github.io/verus/verusdoc/lib/) (if the build succeeds).

You can compile the current documentation by running (in the `verify` directory)
```
RUSTC=../rust/install/bin/rustc RUSTDOC=../rust/install/bin/rustdoc ../rust/install/bin/cargo doc 
```
which will produce documentation files, e.g., `./target/doc/rust_verify/index.html`

## Contributing to the Guide

A work-in-progress tutorial and reference document is automatically published
[📖 here](https://verus-lang.github.io/verus/guide/) from the sources in
[`source/docs/guide`](./source/docs/guide).

## Running tests for the Rust to VIR translation, and inspecting the resulting vir/air/smt

`cargo test` will run the tests for `rust_verify`,

```
RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo test -p rust_verify
```

As discussed above, you may only need the RUSTC variable on macOS/Linux.

You can run a single test file and a specific test within with the following:

```
RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo test -p rust_verify --test <test file> <test name>
```

See the cargo help for more info on the test flags.

If you'd like to inspect the vir/air/smt produced by a test, you can provide a target directory path as an
environment variable, `VERIFY_LOG_IR_PATH`.
You should only run a single test, as only the latest logged IR is preserved.
For example, the following will emit the vir/air/smt logs to `rust_verify/logs`:

```
VERIFY_LOG_IR_PATH="logs" RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo test -p rust_verify --test refs -- test_ref_0
```

If you need to pass additional command-line arguments to the verifier in tests, for example to print the
erased rust ast, you can use the `VERIFY_EXTRA_ARGS` environment variable, like this:

```
VERIFY_EXTRA_ARGS="--print-erased-spec" RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo test -p rust_verify --test refs -- --nocapture test_ref_0
```

