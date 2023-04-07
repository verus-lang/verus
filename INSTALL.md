Below, you can find instructions for:
  * [Building Verus](./INSTALL.md#building-the-project)
  * [Running Verus on the command line](./INSTALL.md#running-the-verifier)
  * [Using Verus in an IDE](./INSTALL.md#ide-support)

# Building the Project

The main project source is in `source`.

`tools` contains scripts for setting up the development environment by
building a `cargo` wrapper that ensures artifacts are built correctly with
our custom build process.

See [`source/CODE.md`](source/CODE.md) for more details about files in `source`.  See the
[official docs](https://rustc-dev-guide.rust-lang.org/) for more about the
normal Rust compiler.

## Step 1: Setup Z3

Change directory to `source`: `cd source`

### On Windows: Make sure the Z3 executable is in your path

Download the [Z3 binaries](https://github.com/Z3Prover/z3/releases).
Make sure you get Z3 4.10.1.
The Z3 `bin` folder contain the executable `z3.exe`.
Either add the Z3 `bin` folder to your path or copy the Z3 executable file to one of the folders in your path.

### On Unix/macOS/Windows: Get a local Z3

From `source`, use the script `./tools/get-z3.sh` (on Unix/macOs) or `./tools/get-z3.ps1` (on Windows) to download Z3.
On Unix/macOS the cargo wrapper will correctly set the `VERUS_Z3_PATH` environment variable for the verifier to find Z3.
If you run the verifier binary manually, set `VERUS_Z3_PATH` to `source/z3` or `source/z3.exe`.

## Step 2: Ensure you have a recent rustup installed

If you don't have it yet, obtain rustup from https://rustup.rs.
We have only tested recent versions (1.25.2); older versions of rustup may behave in way our build
process does not expect.

## Step 3: Build the Verifier

You should be in the `source` subdirectory.

Activate the development environment with `. ../tools/activate` (for bash and zsh), `. ../tools/activate.fish`
(for fish), or `..\tools\activate.bat` or `..\tools\activate.ps1` (on Windows). This will (re-)build `vargo`,
our cargo wrapper, and add it to the `PATH` for the current shell.

Then run `vargo build --release` (omit `--release` for a debug build).

This will build Verus' crates:
- three crates that constitute the verifier:
    - AIR (assertion intermediate language):
      an intermediate language based on assert and assume statements,
      which is translated into SMT queries for Z3
    - VIR (verification intermediate language):
      a simplified subset of Rust,
      which is translated into AIR
    - `rust_verify`, which contains a `main` function that runs Rust and translates
      the Rust intermediate representation into VIR
- three crates that contains built-in definitions and macros used by code being verified:
    - `builtin`
    - `builtin_macros`
    - `states_machines_macros`
- the `vstd` crate, built with Verus itself, that contains Verus' standard library

# Running the Verifier 

After running the build steps above, you can verify an example file.
From the `source` directory, run:

```
vargo run -p rust_verify --release -- rust_verify/example/recursion.rs
```

You can also use the helper script to run the verifier without re-building on **Linux and macOS**:

```
./tools/rust-verify.sh rust_verify/example/recursion.rs
```

This runs the `Rust --> VIR --> AIR --> Z3` pipeline on `recursion.rs`
and reports the errors that Z3 finds.

# IDE Support

**NOTE: These IDE Support instructions are currently outdated, and need to be updated for the new build process.**

Once you have built Verus, you can use it in IDE clients (such as Visual Studio
Code, Emacs, or Vim) that support the LSP protocol.  Follow [these instructions](https://verus-lang.github.io/verus/guide/ide_support.html).

