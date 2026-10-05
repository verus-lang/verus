`verus-exec` creates readable snapshots of executable Verus source. It removes
proof artifacts with the same syntax visitor used by `builtin_macros`, then
applies deletions to the original text. It does not pretty-print or expand
executable code. Comments, spacing, indentation, and line endings outside the
erased regions are preserved. Whole-line annotations and blank lines immediately
inside a removed `verus!` wrapper are removed. A proof expression used as a value
(for example, a match arm body) becomes `{}`, preserving executable control flow.

From `source/`, build the standalone tool with:

```sh
cargo build --release -p verus-exec
```

Snapshot a file to stdout, or write a new file:

```sh
target-verus/release/verus-exec path/to/input.rs
target-verus/release/verus-exec path/to/input.rs -o executable.rs
```

Snapshot a crate by passing its directory or `Cargo.toml`:

```sh
target-verus/release/verus-exec path/to/crate -o /tmp/before
target-verus/release/verus-exec path/to/crate/Cargo.toml -o /tmp/after
diff -ru /tmp/before /tmp/after
```

Crate mode processes every `.rs` file under the input, including module files,
tests, examples, and build scripts, and copies other files unchanged. It skips
the crate's `target` directory and `.git` directories. It does not resolve
dependencies or follow module paths outside the crate directory. The destination
must be new, its parent must exist, and it must be outside the input directory.
Symlinks are rejected. A parse failure leaves no partial crate snapshot. Source
files are never modified.

Both `verus!` and `#[verus_spec(...)]` / `#[verus_verify(...)]` syntax are
supported, including functions in modules, impls, traits, and blocks. Erasure
includes contracts, loop specifications, Verus assertions and assumptions,
proof blocks and ghost locals, spec/proof functions and constants, verifier
attributes, broadcast directives, and `assume_specification`.
`Structural` and `StructuralEq` derives are removed while ordinary Rust derives
are retained. Rust `assert!`, `assert_eq!`, and other executable macros are
preserved.

Snapshots describe source, and are not guaranteed to compile as ordinary Rust.
In particular, named return syntax is retained. Executable `Ghost<T>` and
`Tracked<T>` fields, parameters, and values are retained; adding or changing
them appears in a diff. Imports and ordinary Rust attributes are preserved.
Unrecognized macro payloads are opaque: the tool does not expand arbitrary
macros, evaluate `cfg`, resolve names, or perform the verifier's type-based
erasure. Use the canonical Verus macro and attribute names; renamed imports
cannot be identified without name resolution.

The companion `verus_builtin_macros_syntax` crate compiles the macro visitor's
existing source files as an ordinary library. Recording happens at the visitor's
erasure decisions; source mode bypasses compiler transformations such as
desugaring `for` loops. Keeping this entry point next to the proc-macro
implementation allows syntax changes to be shared without a second parser.

Run the tool's tests with `cargo test -p verus-exec` and its lint checks with
`cargo clippy -p verus-exec --all-targets -- -D warnings`.
