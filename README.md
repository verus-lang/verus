See [Goals](../../wiki/Goals) for a brief description of the project's goals.

## Building the project

The main project source is in `source`.

`tools` contains scripts for setting up the development environment by
cloning a modified version of the rust compiler into a new `rust` directory.
Thus far, we have made only minor modifications to the Rust
compiler, primarily to add additional hooks for the verification code.

See [`source/CODE.md`](source/CODE.md) for more details about files in `source`.  See the
[official docs](https://rustc-dev-guide.rust-lang.org/) for more about the
normal Rust compiler.

### Step 1: Build Rust

On **Linux and macOS**, start in the project root directory and run the [`tools/set-up-rust.sh`](./tools/set-up-rust.sh) script.

On **Windows** you need to perform Step 1 manually:

#### Build the Rust compiler (manually)

Build the rust compiler from [https://github.com/secure-foundations/rust](https://github.com/secure-foundations/rust) with `python x.py install` in the `rust` directory:

```
git clone https://github.com/secure-foundations/rust.git
cd rust
cp config.toml.verify config.toml
python x.py install
```

(Or use python3, if that's what you've got.)

Running `x.py install` creates both a `build` and an `install` directory in the `rust` directory:

```
$ ls
build
install
```

All the installation goes into the project `install` directory;
nothing is installed outside the project directory
(see `prefix = "install"` in `config.toml.verify` for details).

Note: this first step may take more than an hour, since the Rust source code is large, but all other steps are fast.

Change directory back to the project root:

```
cd ..
```

You can pull in future updates to our fork of rust via [`tools/update-rust.sh`](./tools/update-rust.sh).

### Step 2: Setup z3

Change directory to `source`:

```
cd source
```

#### On Windows: make sure the Z3 executable is in your path

Download the [Z3 binaries](https://github.com/Z3Prover/z3/releases).
Make sure you get Z3 4.8.5.
The Z3 `bin` folder contain the executable `z3.exe`.
Either add the Z3 `bin` folder to your path or copy the Z3 executable file to one of the folders in your path.

#### On Unix/macOS: get a local Z3

Use the script `./tools/get-z3.sh` to download Z3.
The `./tools/cargo.sh` script will correctly set the `VERUS_Z3_PATH` environment variable for the verifier to find Z3.
If you run the verifier manually, set `VERUS_Z3_PATH` to `path_to/verify/z3`.

### Step 3: Build the verifier

You should be in the `source` subdirectory.

Set the RUSTC environment variable to point to `../rust/install/bin/rustc` and use `cargo` to build the verifier:

For example, on **macOS and Linux**:
```
RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo build
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

## Running the verifier 


After running the build steps above, you can verify an example file.
From the `source` directory, run:

on **Windows**:

```
../rust/install/bin/rust_verify --pervasive-path pervasive --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/libbuiltin_macros.dll --edition=2018 rust_verify/example/recursion.rs
```

You can also use the helper script on **Linux and macOS**:

```
./tools/rust-verify.sh rust_verify/example/recursion.rs
```

This runs the `Rust --> VIR --> AIR --> Z3` pipeline on `recursion.rs`
and reports the errors that Z3 finds.

The `-L ../rust/install/bin/` is used to link to the `builtin` crate.

## Editing the source code

You should make sure that your check-out of `rust` is up to date.
Use the `./tools/update-rust.sh` script from the project root.

Before committing any changes to the source code,
make sure that it conforms to the `rustfmt` tool's guidelines.
We are using the default `rustfmt` settings from the Rust repository.
To check the source code, type the following from the `source` directory:

```
../rust/install/bin/cargo-fmt -- --check
```

If you have other toolchains installed (with `rustup`) this will run the active
toolchain by default, and not the `rust-fmt` that we compiled with the `rust` compiler.

To switch to the correct tools, you can add the custom toolchain to `rustup`, and set an
override for this project:

```
cd ..
## In the project root:
rustup toolchain link rust-verify rust/install/
rustup override set rust-verify
```

If the source code follows the guidelines, `cargo-fmt -- --check` will produce no output.
Otherwise, it will report suggestions on how to reformat the source code.

To automatically apply these suggestions to the source code, type:

```
../rust/install/bin/cargo-fmt
```

## Documentation

Commenting the code is strongly encouraged.  Use `///` to create comments
that [`rustdoc`](https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html) can
automatically extract into HTML documentation.

You can compile the current documentation by running (in the `verify` directory)
```
RUSTC=../rust/install/bin/rustc RUSTDOC=../rust/install/bin/rustdoc ../rust/install/bin/cargo doc 
```
which will produce documentation files, e.g., `./target/doc/rust_verify/index.html`

## Running tests for the rust to vir translation, and inspecting the resulting vir/air/smt

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
VERIFY_LOG_IR_PATH="logs" RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo test -p rust_verify --test refs_basic test_struct_ref
```

