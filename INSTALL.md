Below, you can find instructions for:
  * [Building Verus](./INSTALL.md#building-the-project)
  * [Running Verus on the command line](./INSTALL.md#running-the-verifier)
  * [Using Verus in an IDE](./INSTALL.md#ide-support)

# Building the Project

The main project source is in `source`.

`tools` contains scripts for setting up the development environment by
cloning a modified version of the rust compiler into a new `rust` directory.
Thus far, we have made only minor modifications to the Rust
compiler, primarily to add additional hooks for the verification code.

See [`source/CODE.md`](source/CODE.md) for more details about files in `source`.  See the
[official docs](https://rustc-dev-guide.rust-lang.org/) for more about the
normal Rust compiler.

## Step 1: Build Rust

### Quick Install (Linux, macOS):

Start in the project root directory and run,

```
tools/set-up-rust.sh
tools/update-rust.sh
```

The first command will download Verus' compiler fork; the second will make sure it is up-to-date and re-compile `rustc`.
You can use the [`tools/update-rust.sh`](./tools/update-rust.sh) script to update the compiler when necessary (when new changes are pushed to the [compiler repository](https://github.com/verus-lang/rust)).

### Manual Install (Linux, macOS, Windows)

Build the rust compiler from [https://github.com/verus-lang/rust](https://github.com/verus-lang/rust) with `python x.py install` in the `rust` directory:

```
git clone https://github.com/verus-lang/rust.git
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

## Step 2: Setup Z3

Change directory to `source`:

```
cd source
```

### On Windows: Make sure the Z3 executable is in your path

Download the [Z3 binaries](https://github.com/Z3Prover/z3/releases).
Make sure you get Z3 4.10.1.
The Z3 `bin` folder contain the executable `z3.exe`.
Either add the Z3 `bin` folder to your path or copy the Z3 executable file to one of the folders in your path.

### On Unix/macOS: Get a local Z3

From `source`, use the script `./tools/get-z3.sh` to download Z3.
The `./tools/cargo.sh` script will correctly set the `VERUS_Z3_PATH` environment variable for the verifier to find Z3.
If you run the verifier manually, set `VERUS_Z3_PATH` to `path_to/verify/z3`.

## Step 3: Build the Verifier

You should be in the `source` subdirectory.

Set the RUSTC environment variable to point to `../rust/install/bin/rustc` and use `cargo build` to build the verifier:

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

# Running the Verifier 

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

# IDE Support

Once you have built Verus, you can use it in IDE clients (such as Visual Studio
Code, Emacs, or Vim) that support the LSP protocol.  Follow [these instructions](https://verus-lang.github.io/verus/guide/ide_support.html).

