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

### On Windows: Get Z3 and set the `VERUS_Z3_PATH` environment variable

Download the [Z3 binaries](https://github.com/Z3Prover/z3/releases).
Make sure you get Z3 4.12.5.
The Z3 `bin` folder contain the executable `z3.exe`.
Set the `VERUS_Z3_PATH` environment variable to the path of the Z3 executable file.

### On Unix/macOS/Windows: Get a local Z3

From `source`, use the script `./tools/get-z3.sh` (on Unix/macOs) or `./tools/get-z3.ps1` (on Windows) to download Z3.
On Unix/macOS the cargo wrapper will correctly set the `VERUS_Z3_PATH` environment variable for the verifier to find Z3.
If you run the verifier binary manually, set `VERUS_Z3_PATH` to `source/z3` or `source/z3.exe`.

## Step 2: Ensure you have a recent rustup installed

If you don't have it yet, obtain rustup from https://rustup.rs.
We have only tested recent versions (1.25.2); older versions of rustup may behave in way our build
process does not expect.

## Step 3: Build Verus

You should be in the `source` subdirectory.

First, activate the development environment with one of the following: (This is automatic for [direnv](https://direnv.net/) users[^1])

```
source ../tools/activate       # for bash and zsh
source ../tools/activate.fish  # for fish
..\tools\activate.bat          # for Windows
..\tools\activate.ps1          # for Windows (Power Shell)
```

This command builds (or re-builds) `vargo`, our cargo wrapper, and adds it to the `PATH` for the current shell.

Now, simply run,

```
vargo build --release
```

(Omit `--release` for a debug build.)

This will build everything you need to use Verus:
- The `rust_verify` binary, which verifies Verus code.
- Additional libraries that Verus code will need to include (`builtin`, `builtin_macros`, and `state_machines_macros`).
- The [Verus standard library, `vstd`](https://verus-lang.github.io/verus/verusdoc/vstd/), which is written in Verus. Our build system builds **and verifies** the `vstd` crate.

If everything is successful, you should see output indicating that various modules in `vstd` are being verified.

# Running the Verifier 

After running the build steps above, you can verify an example file.
From the `source` directory, run:

```
vargo run -p rust_verify --release -- rust_verify/example/vectors.rs
```

This will make sure that the Verus and `vstd` builds are up-to-date, then run the verifier.

You can also run the verifier directly (skipping the up-to-date check) with:

on Linux and macOS:

```
./target-verus/release/verus rust_verify/example/vectors.rs
```

on Windows:

```
.\target-verus\release\verus.exe rust_verify\example\vectors.rs
```

You should see something like the following, indicating that verification was a success:

```
verification results:: verified: 7 errors: 0
```

You can also add the `--compile` flag, which tells Verus to compile the Verus code into a binary via `rustc`. For example:

on Linux and macOS:

```
./target-verus/release/verus rust_verify/example/doubly_linked_xor.rs --compile
./doubly_linked_xor
```

on Windows:

```
.\target-verus\release\verus.exe rust_verify\example\doubly_linked_xor.rs --compile
.\doubly_linked_xor.exe
```
To verify an entire crate, simply point Verus at your `src/main.rs` file for an executable project, or `src/lib.rs` for a library project. You'll need to add `--crate-type=lib` for the latter.

Now you're ready to write some Verus! Check out [our guide](https://verus-lang.github.io/verus/guide/getting_started.html) if you haven't yet.

Note that while `vargo` needs to be run from the `source` directory, the `verus` binary can be run (directly, or via a symlink) from any
directory, which is useful when verifying and compiling a project elsewhere on your file-system.

# IDE Support

Once you have built Verus, you can use it in IDE clients (such as Visual Studio
Code, Emacs, or Vim) that support the LSP protocol.  Follow [these instructions](https://verus-lang.github.io/verus/guide/ide_support.html).

[^1]: If you are a [direnv](https://direnv.net/) user this activation is performed automatically, i.e. you don't need to `source ../tools/activate`; instead, `vargo` will automatically be in your `PATH` as long as you are in the `source` subdirectory.
