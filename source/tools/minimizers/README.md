# Test Case Minimizers

This directory contains a collection of scripts to help automatically minimize
certain kinds of test cases.

## Requirements

+ `creduce`: https://github.com/csmith-project/creduce/blob/master/INSTALL.md
+ Make sure Verus has been built (with `--release` for more speed, if possible)

## How to Use

1. If your issue reproduces in a single file, great!  Otherwise, use [inline-crate](https://crates.io/crates/inline-crate) to convert your crate into a single file automatically.

2. Move the single file to `./foo.rs` (in _this_ directory), since all current scripts assume the file-to-be-minimized is called `./foo.rs`.

3. Find a script in this directory that is useful for your use-case. For example, `./rlimit_exceeded.sh` is a script that considers a test case to be interesting iff it outputs a `Resource limit (rlimit) exceeded`.

4. Confirm that the script works for your use case by running `./rlimit_exceeded.sh && echo "It works" || echo "It does not"` (substitute with your script of choice).

5. Trigger the minimization process: run `creduce ./rlimit_exceeded.sh ./foo.rs`.  If you can use more cores, it helps to use the `--n` flag (e.g., `--n 8` to use 8 cores) to speed things up.

6. Check the new `./foo.rs` (either after creduce finishes, or at any point while it is running) to see a minimized file.

7. If the minimized file is hard to read, running [verusfmt](https://github.com/verus-lang/verusfmt) on it is often helpful to make the minimized file readable again.

## If none of the current minimizers help...

If none of the current minimizers help for your use case, feel free to take inspiration from them, and then contribute your new minimizer back, so as to make future minimization efforts for similar kinds of bugs easier.
