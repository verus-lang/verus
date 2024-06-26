# Tips for Contributing to Verus

Thanks for contributing to Verus!  Verus is an Open Source project and welcomes
contributions.  Please report issues or start discussions here on GitHub.

We use GitHub discussions for feature requests and more open-ended conversations about
upcoming features, and we reserve GitHub issues for actionable issues (bugs) with
existing features. Don't worry though: if we think an issue should be a discussion (or
viceversa) we can always move it later.

## Reporting an issue

Verus has a convenient feature to record an execution run, along with necessary files (including the source to your crate) to help debug and fix issues.  When reporting an issue, we would appreciate if you run Verus with this feature.

To record an execution run, simply add `--record` to the verus command that triggers the issue.  This will produce a `.zip` file (named with the current date/time) that you can attach when opening a GitHub issue.

If you want to aid us in debugging (or are unable to share your full recording, which includes the full crate for us to be able to reproduce your issue), you can attempt to minimize the issue before recording it.  For automatic minimization of a crate or file (producing a smaller file that triggers the same error), see [source/tools/minimizers/README.md](./source/tools/minimizers/README.md) for more details.

## Editing the source code of Verus

Before committing any changes to the source code,
make sure that it conforms to the `rustfmt` and `verusfmt` tool's guidelines.
We are using the default `rustfmt` settings from the Rust repository
(which also apply to the `verusfmt` formatting for the `vstd`).

If you are working on `vstd`, you will need to set up `verusfmt`, which ensures
`verus! { ... }` code has consistent formatting. You can ensures you are on the latest release of verusfmt
by following the [installation instructions](https://github.com/verus-lang/verusfmt/blob/main/README.md#installing-and-using-verusfmt).

To check the Verus and vendored dependencies' source code, and `vstd`'s formatting,
type the following from the `source` directory:

```
vargo fmt -- --check
```

If the source code follows the guidelines, `vargo fmt -- --check` will only produce
`vargo info [0]: formatting <item>` lines.
Otherwise, it will report suggestions on how to reformat the source code, and will
output a non-zero status code.

To automatically apply these suggestions to the source code, type:

```
vargo fmt
```

If you want to use VS Code with `rust-analyzer` to edit the source code of Verus, copy
`.vscode/settings.json.template` to `.vscode/settings.json` and then
edit that file to customize it for your local setup. For instance,
delete `[.exe]` if you're not using Windows and change it to `.exe` if
you are.

### Running `verusfmt` manually

Make sure you are in `source` or one of its subdirectories
(verusfmt picks up the configuration in `source/rustfmt.toml`), and run:

```sh
# To format a specific file
verusfmt <file>.rs

# To format all of vstd at once (on *nix)
find vstd -name \*.rs -print0 | xargs -0 -n1 verusfmt

# To format all of vstd at once (on Windows Powershell)
Get-ChildItem -Path .\vstd -Filter *.rs -Recurse | ForEach-Object { verusfmt $_.FullName }
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

## Internal code documentation

Commenting the code is strongly encouraged.  Use `///` to create comments
that [`rustdoc`](https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html) can
automatically extract into HTML documentation.

You can compile the current documentation by running (in the `source` directory)
```
RUSTC_BOOTSTRAP=1 cargo doc 
```
which will produce documentation files, e.g., `./target/doc/rust_verify/index.html`

## Running tests for the Rust-to-VIR translation, and inspecting the resulting vir/air/smt

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

You may find that every time you run a test it takes minutes to start because
all of Verus is getting rebuilt. This shouldn't happen. If it does, it's
likely because you're running an IDE that uses `rust-analyzer` in the
background, and it's invalidating the build cache. To prevent this, you need
to configure your IDE for Verus development. See above for how to do
this for VS Code.

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

You may sometimes want to verify `vstd` outside of the `vargo` build process: To do so,
build Verus first following the instructions above (with `vargo build --release`) and then
run, from the project root:

```
cd source/vstd
../target-verus/release/verus --crate-type=lib --no-vstd vstd.rs
```

### Common Conventions
Inside `vstd`:
- We add a `lemma_` prefix to the name of a lemma (i.e., a `proof fn`) to make its purpose explicit.
- We try to make lemmas associated functions when possible, e.g., `my_map.lemma_remove_keys_len(keys)`, not `lemma_remove_keys_len(my_map, keys)`.

## Other tips

You can use `--vstd-no-verify` to skip verification of the `vstd` library. This is pretty useful if you're building or running tests a lot. Note that it will still _build_ `vstd`—it just skips the SMT step. For example:

```
# for building
vargo build --vstd-no-verify
# for tests
vargo test --vstd-no-verify -p rust_verify_test --test <test file> <test name>
```
