# Test Case Minimizers

This directory contains a collection of scripts to help automatically minimize
certain kinds of test cases.

## Requirements

+ `creduce`: https://github.com/csmith-project/creduce/blob/master/INSTALL.md
+ Make sure Verus has been built (with `--release` for more speed, if possible)

## How to Use

1. Make sure you can reproduce your issue in a single file. All current scripts assume this file is called `./foo.rs`.

2. Find a script in this directory that is useful for your use-case. For example, `./rlimit_exceeded.sh` is a script that considers a test case to be interesting iff it outputs a `Resource limit (rlimit) exceeded`.

3. Confirm that the script works for your use case by running `./rlimit_exceeded.sh && echo "It works" || echo "It does not"` (substitute with your script of choice).

4. Trigger the minimization process: run `creduce ./rlimit_exceeded.sh ./foo.rs`.

5. Check the new `./foo.rs` (either after creduce finishes, or at any point while it is running) to see a minimized file.

## If none of the current minimizers help...

If none of the current minimizers help for your use case, feel free to take
inspiration from them, and then contribute your new minimizer back, so as to
make future minimization efforts for similar kinds of bugs easier.
