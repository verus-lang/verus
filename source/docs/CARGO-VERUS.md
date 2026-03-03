# Cargo-Verus Overview

This document describes how Verus integrates with Cargo via the `cargo-verus`
binary. It is intended for developers who want to understand, debug, or extend
this integration.

## Overview

`cargo-verus` is a Cargo subcommand that enables verification of Rust code as
part of the normal Cargo workflow. When users run `cargo verus verify`, Cargo
locates the `cargo-verus` binary and invokes it as an extension.

**Key principle**: cargo-verus is a thin wrapper that translates Cargo metadata
and user arguments into environment variables, then invokes `cargo build` with
the `RUSTC_WRAPPER` environment variable set to the `verus` binary. The verus
driver performs the actual verification.

## Architecture

```
User: cargo verus verify -p my_crate --release -- --rlimit=60
    ↓
cargo-verus binary
    ├─ Parses arguments
    ├─ Queries cargo metadata
    ├─ Sets environment variables for each package
    └─ Invokes: cargo build -p my_crate --release
        with RUSTC_WRAPPER=/path/to/verus
    ↓
Cargo build system
    └─ For each crate compilation:
        Invokes: /path/to/verus /path/to/rustc [rustc-args]
    ↓
verus binary (rust_verify driver)
    ├─ Reads environment variables
    ├─ Decides whether to verify or pass through to rustc
    ├─ If verifying: runs verification pipeline
    └─ Exports .vir file for dependents
```

## Entry Points

### cargo-verus binary

**File**: `cargo-verus/src/main.rs`

The `main()` function:
1. Detects whether invoked as `cargo-verus` or `cargo verus`
2. Extracts arguments after the subcommand name
3. Routes to `process()` which creates a `VerusCmd` and executes it

### verus binary (as RUSTC_WRAPPER)

**File**: `rust_verify/src/main.rs`

When invoked via cargo:
1. Detects `VERUS_DRIVER_VIA_CARGO=1` environment variable
2. Expects first argument to be path to `rustc` (per [`RUSTC_WRAPPER`
   protocol](https://doc.rust-lang.org/cargo/reference/environment-variables.html))
3. Calls `extend_args_and_check_is_direct_rustc_call()` to unpack environment
   variables
4. Decides whether to verify based on `VERUS_DRIVER_VERIFY_{package_id}` environment variable

## Command Line Argument Handling

### Argument Separation

Arguments are split into two categories:

1. **Cargo arguments** (before `--`): Passed to cargo (e.g., `--release`, `-p crate_name`, `--features`)
2. **Verus arguments** (after `--`): Passed to verus driver (e.g., `--rlimit=60`, `--expand-errors`)

Example:
```bash
cargo verus verify -p my_crate --release -- --rlimit=60 --expand-errors
#                  ^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^
#                  Cargo arguments            Verus arguments
```

## Environment Variables

Environment variables are the primary communication mechanism between
cargo-verus and the verus driver. This approach is necessary because:
- Cargo's `RUSTC_WRAPPER` invokes verus as a subprocess
- Environment variables pass naturally to subprocesses
- They enable per-package configuration

### Variable Reference

| Variable                              | Purpose                                                | Set By      | Read By      |
|---------------------------------------|--------------------------------------------------------|-------------|--------------|
| `VERUS_DRIVER_VIA_CARGO`              | Indicates cargo-verus invocation                       | cargo-verus | verus driver |
| `VERUS_DRIVER_ARGS`                   | Common Verus args for all packages                     | cargo-verus | verus driver |
| `VERUS_DRIVER_ARGS_FOR_{id}`          | Per-package Verus args                                 | cargo-verus | verus driver |
| `VERUS_DRIVER_VERIFY_{id}`            | "1" if package should be verified                      | cargo-verus | verus driver |
| `VERUS_DRIVER_IS_BUILTIN_{id}`        | "1" if package is `verus_builtin`                      | cargo-verus | verus driver |
| `VERUS_DRIVER_IS_BUILTIN_MACROS_{id}` | "1" if package is `builtin_macros`                     | cargo-verus | verus driver |
| `RUSTC_WRAPPER`                       | Path to verus binary                                   | cargo-verus | cargo        |
| `__CARGO_DEFAULT_LIB_METADATA`        | Trigger cargo rebuild when exported .vir file changes  | cargo-verus | cargo        |

### Package ID Generation

Package IDs are generated to be unique across workspaces:

```rust
fn mk_package_id(name, version, manifest_path) -> String {
    let hash = SHA256(manifest_path)[0:12];
    format!("{}-{}-{}", name, version, hash)
}
```

### Argument Packing

Arguments are packed into environment variables using a separator:

```
VERUS_DRIVER_ARGS_SEP = "__VERUS_DRIVER_ARGS_SEP__"
```

Format: `[SEP, arg1, SEP, arg2, ...]`

Example:
```
__VERUS_DRIVER_ARGS_SEP__--rlimit=60__VERUS_DRIVER_ARGS_SEP__--expand-errors
```

This preserves arguments containing spaces or special characters.

## Cargo.toml Configuration

Packages opt into verification via `[package.metadata.verus]`:

```toml
[package.metadata.verus]
verify = true
```

### Available Options

| Field                | Type | Default | Purpose                              |
|----------------------|------|---------|--------------------------------------|
| `verify`             | bool | false   | Enable verification for this crate   |
| `no_vstd`            | bool | false   | Don't import vstd                    |
| `is_vstd`            | bool | false   | This crate is vstd itself            |
| `is_core`            | bool | false   | This crate is the core library       |
| `is_builtin`         | bool | false   | This crate is `verus_builtin`        |
| `is_builtin_macros`  | bool | false   | This crate is `builtin_macros`       |

### Parsing

The `VerusMetadata` struct is deserialized from the `package.metadata.verus`
JSON object in Cargo's metadata output.

## Dependency Resolution

### MetadataIndex

cargo-verus builds an index of all packages and their dependencies:

```rust
struct MetadataIndex<'a> {
    entries: BTreeMap<&'a PackageId, MetadataIndexEntry<'a>>,
}

struct MetadataIndexEntry<'a> {
    package: &'a Package,
    verus_metadata: VerusMetadata,
    deps: BTreeMap<&'a str, &'a NodeDep>,
}
```

### Import Dependency Detection

For each verified package, cargo-verus:
1. Iterates its dependencies
2. Checks if each dependency has `verify = true`
3. Adds `--VIA-CARGO import-dep-if-present={dep_name}` to that package's args

This tells the verus driver which dependencies may have `.vir` files to import.

## VIR File Management

### Export

When a package is verified, its VIR (Verification Intermediate Representation) is exported:

**Location**: Same directory as `.rlib`, with `.vir` extension, e.g.,
```
target/debug/deps/libmy_crate-xxxxx.rlib
target/debug/deps/libmy_crate-xxxxx.vir
```

**Process** (in `rust_verify/src/import_export.rs`):
1. Prune AST to exported items only
2. Remove function bodies for non-public spec functions
3. Serialize with `bincode`

### Import

When verifying a package with dependencies:

1. The `handle_externs()` function receives the list of external crates from rustc
2. For each crate in `import_dep_if_present`:
   - Locates the `.rlib` file
   - Checks if a corresponding `.vir` file exists
   - If found, adds it to the import list
3. The verifier deserializes and merges imported VIR

### Build Fingerprinting

In cargo-verus/src/main.rs, we run:
```rust
cmd.env("__CARGO_DEFAULT_LIB_METADATA", "verus");
```
This ensures that Cargo's fingerprinting system detects when `.vir` files
change, triggering rebuilds of dependent crates.

## Execution Flow

### Detailed Flow for `cargo verus verify -p my_crate`

1. **cargo-verus main()**
   - Parse arguments: `["verify", "-p", "my_crate"]`
   - Create `VerusCmd` with `cargo_args = ["-p", "my_crate"]`, `verify = true`

2. **VerusCmd::into_std_cmd()**
   - Query cargo metadata for all packages
   - Build `MetadataIndex`
   - For each package with `verify = true`:
     - Set `VERUS_DRIVER_VERIFY_{id} = "1"`
     - For each verified dependency, add import-dep-if-present arg
   - Set `RUSTC_WRAPPER = /path/to/verus`
   - Return `cargo build -p my_crate` command

3. **Cargo execution**
   - Cargo resolves dependencies and build order
   - For each crate compilation, invokes `RUSTC_WRAPPER`

4. **verus driver invocation** (per crate)
   - Detect `VERUS_DRIVER_VIA_CARGO = "1"`
   - Unpack `VERUS_DRIVER_ARGS` and `VERUS_DRIVER_ARGS_FOR_{id}`
   - Check `VERUS_DRIVER_VERIFY_{id}`
   - If verifying:
     - Import dependency VIR files
     - Run verification pipeline
     - Export VIR file
   - Else: pass through to rustc

## Design Decisions

### Why Environment Variables?

- Faster than file I/O for each rustc invocation
- Automatic cleanup when cargo process exits
- Avoids file locking issues on parallel builds

### Why Per-Package Environment Variables?

- Allows different flags for different crates (e.g., `--is-vstd` only for vstd)
- Avoids unnecessary rebuilds when common args change
- Scales to large workspaces

### Why the Argument Separator?

- Preserves arguments with spaces: `--smt-options="foo bar"`
- Prevents shell interpretation issues
- Works reliably across platforms

### Why Store .vir Files in Target Directory?

- Automatic cleanup with `cargo clean`
- Partitioned per build variant (debug/release)
- Integrated with Cargo's fingerprinting

## Common Developer Tasks

### Adding a New Cargo.toml Option

1. Add field to `VerusMetadata` struct in `cargo-verus/src/main.rs`
2. The field will be automatically parsed from `[package.metadata.verus]`
3. Use the field when setting environment variables in `VerusCmd::into_std_cmd()`
4. Read the environment variable in verus driver

### Adding a New Environment Variable

1. Add constant in `cargo-verus/src/main.rs`
2. Add matching constant in `rust_verify/src/cargo_verus.rs`
3. Set the variable in `VerusCmd::into_std_cmd()`
4. Read in `extend_args_and_check_is_direct_rustc_call()` or `handle_externs()`

### Adding a New Command

1. Add to match in `VerusCmd::new()` (around line 202)
2. Implement command-specific logic
3. Update help text

### Debugging cargo-verus Issues

1. Run with `CARGO_LOG=cargo::ops::cargo_compile=trace` for cargo debug output
2. Print environment variables set by cargo-verus
3. Run verus driver directly with same environment to isolate issues
4. Check `.vir` file locations in target directory

## File Reference


| File                                           | Purpose                                                      |
|------------------------------------------------|--------------------------------------------------------------|
| `cargo-verus/src/main.rs`                      | Main cargo-verus binary, argument parsing, metadata handling |
| `rust_verify/src/main.rs`                      | Verus driver entry point, `RUSTC_WRAPPER` detection          |
| `rust_verify/src/cargo_verus.rs`               | Environment variable unpacking, extern handling              |
| `rust_verify/src/cargo_verus_dep_tracker.rs`   | Dependency tracking for incremental builds                   |
| `rust_verify/src/import_export.rs`             | VIR serialization/deserialization                            |
| `rust_verify/src/config.rs`                    | Argument parsing including cargo-specific args               |
