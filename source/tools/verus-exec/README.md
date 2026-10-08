`verus-exec` creates readable snapshots of executable Verus source. It removes
proof artifacts with the same syntax visitor used by `builtin_macros`, then
applies edits to the original text. Comments, spacing, indentation, and line
endings outside the erased or expanded regions are preserved. Whole-line
annotations and blank lines immediately
inside a removed `verus!` wrapper are removed. A proof expression used as a value
(for example, a match arm body) becomes `{}`, preserving executable control flow.
Expression macro wrappers become parentheses, retaining operator precedence;
statement terminators are added where needed. Contracted constants and statics
retain their initializer blocks using Rust's `= { ... };` syntax.

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

Git worktree `.git` files are skipped too. Use repeatable `--exclude` arguments
to skip relative paths, including custom build directories and local symlinked
launchers:

```sh
target-verus/release/verus-exec path/to/crate -o /tmp/snapshot \
    --exclude target-custom --exclude verus
```

Both `verus!` and `#[verus_spec(...)]` / `#[verus_verify(...)]` syntax are
supported, including functions in modules, impls, traits, and blocks. Erasure
includes contracts, loop specifications, Verus assertions and assumptions,
proof blocks and ghost locals, spec/proof functions and constants, verifier
attributes, broadcast directives, and `assume_specification`.
Items marked with `#[cfg(verus_keep_ghost)]` are removed, including imports,
modules, impls, and associated items. Other `cfg` conditions are retained.
Named return bindings become ordinary Rust return types:
`fn clone(&self) -> (result: Self)` becomes `fn clone(&self) -> Self`.
`Structural` and `StructuralEq` derives are removed while ordinary Rust derives
are retained. Rust `assert!`, `assert_eq!`, and other executable macros are
preserved.

The tool expands `struct_with_invariants!`, `atomic_with_ghost!`,
`state_machine!`, `tokenized_state_machine!`, and `tokenized_state_machine_vstd!`
using the existing macro parsers and generators in exec-only mode.
Structs and state-machine token types become ordinary Rust declarations;
atomic operations become blocks that evaluate the receiver and operands once,
in order, and invoke the underlying atomic operation. Ghost update blocks are
discarded. Generated code retains its `vstd` dependencies.
Only expanded sections are pretty-printed, with the surrounding indentation
and line endings. Comments inside macro payloads are lost unless represented
as attributes, such as doc comments. Ordinary executable source around them
keeps its original formatting. Expansion always selects exec-only behavior,
independently of the environment used to build or run the tool.

Executable `Ghost<T>` and `Tracked<T>` fields, parameters, and return types are
retained; adding or changing them appears in a diff. Their constructors use the
macro visitor's existing `assume_new_fallback(|| unreachable!())` lowering,
discarding the ghost argument without evaluating it. Type arguments and comments
outside the discarded argument list retain their source text.
Supported `Ghost(x)` and `Tracked(x)` patterns in function parameters and local
`let` bindings become temporary identifiers, using the same pattern rewriter
as the compiler. The generated names avoid existing source identifiers, including
raw identifiers and names in opaque macros. Surrounding pattern comments, type
annotations, and executable bindings keep their source text. Wrapper recognition
uses bare canonical names; qualified or renamed constructors and patterns are
not resolved.

Snapshots describe source, and are not guaranteed to compile as ordinary Rust.
Imports and ordinary Rust attributes
are preserved unless their item has `#[cfg(verus_keep_ghost)]`.
Unrecognized macro payloads are opaque: the tool does not expand arbitrary
macros, evaluate general `cfg` expressions, resolve names, or perform the
verifier's type-based erasure. Use the canonical Verus macro and attribute names;
renamed imports cannot be identified without name resolution.
This includes invocations of known Verus macros inside other opaque macro
payloads, such as `assert_eq!(atomic_with_ghost!(...), value)`.
A successful snapshot therefore does not certify
that every proof artifact was removed or that arbitrary proof edits leave
the snapshot unchanged.

Qualified macro and derive names are recognized through `verus_builtin_macros`,
`builtin_macros`, `verus_state_machines_macros`, and `vstd`; similarly named macros
in other namespaces stay
opaque. Conditional mode attributes are not evaluated, so `cfg_attr` that changes
an item between exec and ghost modes cannot be classified without choosing a
configuration.

The companion `verus_builtin_macros_syntax` crate compiles the macro visitor's
existing source files as an ordinary library. Recording happens at the visitor's
erasure decisions; source mode bypasses compiler transformations such as
desugaring `for` loops. Keeping this entry point next to the proc-macro
implementation allows syntax changes to be shared without a second parser.
The `verus_state_machines_macros_syntax` companion similarly shares the
state-machine parser and generator with its proc-macro crate.

Run the tool's tests with `cargo test -p verus-exec` and its lint checks with
`cargo clippy -p verus-exec --all-targets -- -D warnings`.
The tests include ordinary Cargo compilation and execution of the same program
before and after extraction, covering wrapper lowering, discarded argument
side effects, temporary-name collisions, all supported atomic operations, and
generated struct/token types.
