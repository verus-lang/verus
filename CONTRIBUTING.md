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

## User-facing documentation

The CI publishes some user facing documentation, including the ["verusdoc" (modified rustdoc) of `vstd`](https://verus-lang.github.io/verus/verusdoc/vstd/), as well as a [tutorial guide](https://verus-lang.github.io/verus/guide/).

To manually build the `vstd` documentation, run,

```
cd source
./tools/docs.sh
```

The output of the command will tell you where the HTML is generated.

Meanwhile, the tutorial guide can be found in `source/docs/guide/`. From that directory, run `mdbook serve` to run a local webserver to render the guide as HTML.

## Internal Code Documentation

Commenting the code is strongly encouraged.  Use `///` to create comments
that [`rustdoc`](https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html) can
automatically extract into HTML documentation.

You can compile the current documentation by running (in the `source` directory)
```
RUSTC_BOOTSTRAP=1 cargo doc 
```
which will produce documentation files, e.g., `./target/doc/rust_verify/index.html`

## Running tests for the Rust to VIR translation, and inspecting the resulting vir/air/smt

`vargo test` will run the tests for `rust_verify_test`,

```
vargo test -p rust_verify_test
```

You can run a single test file and a specific test within with the following:

```
vargo test -p rust_verify_test --test <test file> <test name>
```

`vargo nextest run` is also supported. To install `nextest`, see [https://nexte.st/book/installation.html](https://nexte.st/book/installation.html).

See the cargo help for more info on the test flags.

If you need to pass additional command-line arguments to the verifier in tests, for example to print the
erased rust ast, you can use the `VERUS_EXTRA_ARGS` environment variable, like this:

```
VERUS_EXTRA_ARGS="--print-erased-spec" vargo test -p rust_verify_test --test refs -- --nocapture test_ref_0
```

It can be useful to inspect the intermediate representations used by Verus (VIR, AIR, SMTLIB);
you can log the VIR, AIR, and SMTLIB for a test with:

```
VERUS_EXTRA_ARGS="--log-all" vargo test -p rust_verify_test --test refs -- --nocapture --exact test_ref_0
```

This will output the log files in `rust_verify_test/.verus-log`. Only run one test at
a time when using this flag, so that the logs are not overwritten by other tests.

## Contributing to the standard library (`vstd`)

If you're contributing to the standard library, you should also test the
standalone build of that library with
```
cd source/vstd
cargo build
```

A common error you'll find at this stage is that imports of specific
identifiers with `use` (as opposed to blanket imports using `*`) don't work
when building the standalone exec-only version of `vstd`. To rectify this error,
make sure every such import is prefixed by `#[cfg(verus_keep_ghost)]`, as
in the following example:
```
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::general_internals::is_le;
```

## Other tips

You can use `--vstd-no-verify` to skip verification of the `vstd` library. This is pretty useful if you're building or running tests a lot. Note that it will still _build_ `vstd`—it just skips the SMT step. For example:

```
# for building
vargo build --vstd-no-verify
# for tests
vargo test --vstd-no-verify -p rust_verify_test --test <test file> <test name>
```


## Automatically minimizing an issue/error example

If you have a large file that produces some sort of error in Verus, you can automatically minimize it to a smaller/simpler file that produces the same error. See [source/tools/minimizers/README.md](./source/tools/minimizers/README.md) for more details.
