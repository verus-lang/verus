# Using Verus via Cargo

For projects with multiple crates, Verus provides a `cargo verus` subcommand
that integrates verification into the normal Rust Cargo workflow.

## Prerequisites

The `cargo-verus` binary must be in your `PATH`. It is included in the official
[Verus release packages](https://github.com/verus-lang/verus/releases) alongside the
`verus` binary.

Check that it is available by running:

```
cargo verus --help
```

## Starting a new project

The fastest way to create a new Verus project is:

```bash
# Binary project
cargo verus new --bin my_project

# Library project
cargo verus new --lib my_library
```

This creates a new directory with a correctly-configured `Cargo.toml`, an initial
`src/main.rs` (or `src/lib.rs`), and a `.gitignore`. The generated project already has
`vstd` as a dependency and the `[package.metadata.verus]` section described below.

## Cargo.toml configuration

Crates that should be verified must opt in by adding a `[package.metadata.verus]`
section to their `Cargo.toml`:

```toml
[package.metadata.verus]
verify = true
```

### Suppressing the `verus_only` lint

Verus enables a `verus_only` cfg flag during verification so that `use` statements for
ghost items can be guarded with `#[cfg(verus_only)]`. Since this flag is not declared in
`Cargo.toml`, Rust 1.80+ will emit a warning unless you suppress it:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ['cfg(verus_only)'] }
```

`cargo verus new` adds this automatically. See [Ghost Erasure](./erasure.md) for a full
explanation of `verus_only` and when to use it.

## Subcommands

### `cargo verus verify`

Runs verification on all crates that have `verify = true`, including dependencies.
Does **not** produce a compiled binary.

```bash
cargo verus verify              # Verify all of the crates
cargo verus verify -p my_crate  # Verify only my_crate and its dependencies
```

Use `verify` for day-to-day proof development. Incremental builds mean that only
changed crates are re-verified.

### `cargo verus focus`

Like `verify`, but skips re-verification of dependencies. Useful when you are only
iterating on root crates and their dependencies have not changed.

```bash
# Verify all of the root crates, but not their dependencies
cargo verus focus
# Verify my_crate, but not its dependencies
cargo verus focus -p my_crate
```

Dependencies are still *built* (so their types are available), but their proofs are
not re-checked. `cargo verus verify` should be used before committing to ensure the project's
end-to-end proof is sound.

### `cargo verus build`

Verifies all opted-in crates **and** compiles them to native artifacts (libraries or
binaries). Use this when you want to ship a verified binary.

```bash
cargo verus build
cargo verus build --release
```

Note that Verus-annotated code can also be built with a normal `cargo build` command, if you prefer.


## Passing arguments

Arguments are split around `--`:

- **Before `--`**: forwarded to `cargo` 
- **After `--`**: forwarded to every `verus` invocation

```bash
cargo verus verify -p my_crate --release -- --rlimit 60 --expand-errors
#                  ^^^^^^^^^^^^^^^^^^^^^    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#                  Cargo arguments            Verus arguments
```

Common Verus arguments that can be passed this way include `--rlimit`,
`--expand-errors`, and `--log-all`.  You should typically avoid passing
crate-specific arguments this way.  For example, passing `--verify-module`
or `--verify-function` is unlikely to work, unless you have the same module/function
in every verified crate in your project and its dependencies.  To pass these
project-specific flags, see below for how to control which crates receive
which the Verus arguments.

### Controlling which crates receive Verus arguments

By default, the Verus arguments after `--` are forwarded to **all** verified crates.
Use `--fwd-verus-args-to <target>` to narrow or widen the target.

| Value    | Effect                                                         |
|----------|----------------------------------------------------------------|
| `all`    | Forward to all verified crates, including dependencies (default for `verify`, `build`) |
| `roots`  | Forward only to the root (selected) crates (default for `focus`) |
| `deps`   | Forward only to dependency crates, not to root crates          |

```bash
# Only pass --rlimit to the root crate, not to its verified dependencies
cargo verus verify --fwd-verus-args-to roots -- --rlimit 60
```

Recall that you can also use the standard `cargo -p <crate_name>` to restrict
operation to a single crate (and potentially its dependencies).

## Multi-crate workspaces

In a workspace, each crate that should be verified must independently opt in by adding
`verify = true` to its `Cargo.toml` file. Crates without that setting are
compiled normally and are not passed through the Verus prover.

```bash
# Verify the entire workspace
cargo verus verify --workspace

# Verify a single crate and its verified dependencies
cargo verus verify -p my_crate
```

## Incremental verification

cargo-verus stores `.vir` files next to the compiled `.rlib` artifacts in the `target`
directory. Cargo's fingerprinting system detects when these files change and
automatically re-verifies downstream crates. Running `cargo clean` removes all
verification artifacts.
