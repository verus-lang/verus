### Updating the code forked form rustc

First, download the rust repository somewhere on your machine:

```
git clone https://github.com/rust-lang/rust/
```

Now `cd` back go the Verus repository that you want to apply the changes to. For the next step, you'll need to know the rustc version you're updating from and to. Run:

```
./source/tools/update-rustc-forks.sh /path/to/rust <old> <new>
```

Rust uses the version numbers as tags, so for example, if you're trying to update from 1.88.0 to 1.89.0, you can just do:

```
./source/tools/update-rustc-forks.sh /path/to/rust 1.88.0 1.89.0
```

This script will create a diff of all the relevant code and fetch it into your repository. If the script is successful, you'll see output like:

```
Diff prepared. When you're ready to apply it, run:
git cherry-pick <some commit hash>
```

### Tips for resolving any conflicts

In our fork, all the dependencies from the `rustc_mir_build/Cargo.toml` file were moved to be `extern crate` lines in `rustc_mir_build/src/lib.rs` file.  So if you see any conflicts in `Cargo.toml`, you may need to modify `lib.rs`.
