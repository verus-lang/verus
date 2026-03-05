These instructions are for installing Verus using the binary releases, intended for most people who plan to use Verus from the command line.

If you'd rather use the **VSCode IDE**, you should instead read the instructions [here](https://verus-lang.github.io/verus/guide/getting_started_vscode.html).

If you're a **Verus developer**, or if you're looking for a **specific commit version**, you'll need to install from source. See [BUILD.md](./BUILD.md).

# Support

Verus provides first-tier support to relatively recent OS distributions (MacOS, Windows and Ubuntu).
The general rule of thumb is that we lag Github's `<os>-latest` by one version.
These are the architectures that have release artifacts prebuilt:
- MacOS 14 (arm)
- MacOS 15 (x86_64)
- Windows 2022 (x86_64)
- Ubuntu 22.04 (x86_64)

Otherwise, you may have to build `verus` from source (see the [build instructions](./BUILD.md)).

# Installing Verus

## 1. Download the binary release.

You can select from either:

 * **(Recommended)** The weekly point releases. You can get the latest at  [https://github.com/verus-lang/verus/releases/latest](https://github.com/verus-lang/verus/releases/latest)

 * The rolling release, which tracks the latest commit on `main`.
   This can be found on our [release page](https://github.com/verus-lang/verus/releases), marked "pre-release".


After selecting the desired release, open the "Assets" drawer from the releases page and download the file appropriate to your platform.

## 2. Unzip the file

Unzip the file and navigate into the resulting directory. In bash, for example:

```
unzip verus-0.2025.06.24.77d5bbe-x86-macos.zip
mv verus-x86-macos verus
cd verus
```

The remainder of these instructions assume this is your working directory.

## 3. (MacOS Only) Remove Gatekeeper quarantine

If you're on MacOS, the binaries and libraries will be quarantined by Gatekeeper, which will pop up a number of messages about running software downloaded from the internet. We provide a script to fix this automatically. You can inspect the script first, if you'd like.

From the directory in the previou step:

```
bash macos_allow_gatekeeper.sh
```

## 4. Install the correct Rust toolchain

To check if this step is necessary, run `./verus`.  It may print an error telling you to install `rustup`, or to install the necessary toolchain. If so, it will output instructions on what to install and how to install it. Repeat until Verus doesn't report any such error.

For example, if `rustup` is not available, you'll see something like:

```
$ ./verus
verus: rustup not found, or not executable
verus needs a rustup installation
run the following command (in a bash-compatible shell) to install rustup:
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain 1.86.0-x86_64-unknown-linux-gnu
or visit https://rustup.rs/ for more information
```

Follow these instructions to obtain `rustup` and the current version of the toolchain used by Verus, then run `verus` again.

If `rustup` has been installed, but the necessary toolchain has _not_ been installed, then when you run `./verus` will instead print:

```
$ ./verus
verus: required rust toolchain 1.86.0-x86_64-unknown-linux-gnu not found
run the following command (in a bash-compatible shell) to install the necessary toolchain:
  rustup install 1.86.0-x86_64-unknown-linux-gnu
error: toolchain '1.86.0-x86_64-unknown-linux-gnu' is not installed
```

Follow the instructions to install the necessary toolchain.

## 5. Start using Verus!

You can now run `./verus` to verify and compile verus files and projects.

Now you're ready to write some Verus! Check out [our guide](https://verus-lang.github.io/verus/guide/getting_started.html) if you haven't yet.
