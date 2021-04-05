This directory contains an experimental project for formally verifying Rust-like code.
It is currently unfinished and under construction.
See [Goals](../../../wiki/Goals) for a brief description of the project's goals.

# Building the project

The project root directory contains the following subdirectories:

```
.github
compiler
library
src
verify
```

All but the `verify` subdirectory come from the Rust source code.

## Step 1: build Rust

Start in the project root directory.
Create a `config.toml` file based on `config.toml.verify`, and run `x.py install`:

```
cp config.toml.verify config.toml
python x.py install
```

Running `x.py install` creates both a `build` and an `install` directory in the project root directory:

```
.github
build
compiler
install
library
src
verify
```

All the installation goes into the project `install` directory;
nothing is installed outside the project directory
(see `prefix = "install"` in `config.toml.verify` for details).

Note: this first step may take more than an hour, since the Rust source code is large, but all other steps are fast.

## Step 2: copy the Z3 libraries into install directory

Download the [Z3 binaries](https://github.com/Z3Prover/z3/releases).
The Z3 `bin` folder contain the libraries `libz3.*`.
The easiest way to make these libraries available to the build is to copy them into the `install` directory.
For example, on Windows:

```
cp /z3/bin/libz3.lib install/lib/rustlib/x86_64-pc-windows-msvc/lib
cp /z3/bin/libz3.dll install/bin
```

## Step 3: build the verifier

First, go to the `verify` subdirectory:

```
cd verify
```

Then use `cargo` to build the verifier:

```
../install/bin/cargo build
```

This will build four crates:
- three crates that constitute the verifier:
    - AIR (assertion intermediate language):
      an intermediate language based on assert and assume statements,
      which is translated into SMT queries for Z3
    - VIR (verification intermediate language):
      a simplified subset of Rust,
      which is translated into AIR
    - rust_verify, which contains a `main` function that runs Rust and translates
      the Rust intermediate representation into VIR
- one crate that contains built-in definitions used by code being verified:
    - builtin

# Running the verifier 

After running the build steps above, you can verify an example file.
From the `verify` directory, run:

```
../install/bin/rust_verify rust_verify/examples/basic.rs -L ../install/bin/
```

This runs the `Rust --> VIR --> AIR --> Z3` pipeline on `basic.rs`
and reports the errors that Z3 finds.

The `-L ../install/bin/` is used to link to the `builtin` crate.

# Editing the source code

Before committing any changes to the source code,
make sure that it conforms to the `rustfmt` tool's guidelines.
We are using the default `rustfmt` settings from the Rust repository.
To check the source code, type the following from the `verify` directory:

```
../install/bin/cargo-fmt -- --check
```

If the source code follows the guidelines, `cargo-fmt -- --check` will produce no output.
Otherwise, it will report suggestions on how to reformat the source code.

To automatically apply these suggestions to the source code, type:

```
../install/bin/cargo-fmt
```
