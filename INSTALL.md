Below, you can find instructions for:
  * [Obtaining Verus and Rust](./INSTALL.md#obtaining-verus-and-rust)
  * [Using Verus in an IDE](./INSTALL.md#ide-support)

## Obtaining Verus and Rust

You can obtain a binary release of Verus from [https://github.com/verus-lang/verus/releases](https://github.com/verus-lang/verus/releases). At the moment we only offer rolling binary releases that track the latest commit on `main`. If you need a specific older version, you can build it yourself using the instructions in [BUILD.md](./BUILD.md).

On that page, open the "Assets" drawer and download the release for your platform, then unpack the zip file in a convenient location, e.g. `~/verus`. We will use this path as an example for the following, but you can replace it with your preferred location.

*If you're on MacOS* the binaries and libraries will be quarantined by Gatekeeper, which will pop up a number of messages about running software downloaded from the internet. To avoid this issue, once you have unpacked the `zip` file, open a shell in the newly unzipped directory and run `bash macos_allow_gatekeeper.sh`, which will remove the Gatekeeper quarantine flag from all the relevant files (you can inspect the file first, if you'd like, it only makes changes inside the directory you just unpacked).

`~/verus` now contains a binary distribution of Verus, which depends on a distribution of the currently supported version of Rust, installed via `rustup`. If you run `~/verus/verus` it will check if `rustup` and the correct toolchain are available and print a message accordingly.

For example, if rustup is not available, you'll see something like:

```
$ ~/verus/verus 
verus: rustup not found, or not executable
verus needs a rustup installation
run the following command (in a bash-compatible shell) to install rustup:
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain 1.82.0-x86_64-unknown-linux-gnu
or visit https://rustup.rs/ for more information
```

Follow these instructions to obtain rustup and the current version of the toolchain used by Verus, then run `verus` again.

When you update `verus`, or if you already had `rustup` installed, the necessary toolchain may not be installed, and running `~/verus/verus` will instead print:

```
$ ~/verus/verus
verus: required rust toolchain 1.82.0-x86_64-unknown-linux-gnu not found
run the following command (in a bash-compatible shell) to install the necessary toolchain:
  rustup install 1.82.0-x86_64-unknown-linux-gnu
error: toolchain '1.82.0-x86_64-unknown-linux-gnu' is not installed
```

Follow the instructions to install the necessary toolchain.

You can now run `~/verus/verus` to verify and compile verus files and projects.

Now you're ready to write some Verus! Check out [our guide](https://verus-lang.github.io/verus/guide/getting_started.html) if you haven't yet.

# IDE Support

Once you have built or installed Verus, you can use it in IDE clients (such as Visual Studio Code, Emacs, or Vim) that support the LSP protocol.  Follow [these instructions](https://verus-lang.github.io/verus/guide/ide_support.html).
