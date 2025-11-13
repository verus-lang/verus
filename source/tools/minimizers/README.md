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

## Configuration

All scripts support these environment variables for customization:

- **`TIMEOUT=30`** - Set a different timeout in seconds (default varies by script)
- **`TRACE=1`** - Enable bash tracing for debugging the scripts

Example:
```bash
TIMEOUT=60 TRACE=1 ./verified_minimal.sh
```

## Available Minimizers

### Error Minimizers

These scripts help minimize test cases that produce specific errors:

- **`panicked_in.sh`** - Minimizes code that causes panics (searches for `"panicked at"`)
- **`rlimit_exceeded.sh`** - Minimizes code that hits resource limits
- **`time_exceeded.sh`** - Minimizes code that takes too long to verify

### Extracting Verified Examples

Beyond minimizing failing test cases, you can also use these tools to extract small verified examples from large codebases:

#### `verified_minimal.sh`
Reduces code to a minimal verified example. Useful for extracting clean examples from complex projects.

**Example:**
```bash
creduce --n 8 ./verified_minimal.sh ./foo.rs
```

#### `verified_with_invariant.sh`
Extracts minimal examples that use type invariants. Great for creating focused examples of this feature.

**Example:**
```bash
creduce ./verified_with_invariant.sh ./foo.rs
```

#### `verified_with_spec.sh`
Extracts minimal examples that contain spec functions. Useful for demonstrating spec/exec separation.

**Example:**
```bash
creduce ./verified_with_spec.sh ./foo.rs
```

#### `verified_with_feature.sh`
General-purpose script for extracting examples with specific Verus features.

**Required environment variable:**
- `FEATURE="pattern"` - Regular expression pattern to search for

**Examples:**
```bash
# Extract minimal example with proof functions
FEATURE="proof fn" creduce ./verified_with_feature.sh ./foo.rs

# Extract minimal example with loop invariants
FEATURE="loop_invariant" creduce ./verified_with_feature.sh ./foo.rs

# Extract minimal example with spec functions returning bool
FEATURE="spec fn.*->.*bool" creduce ./verified_with_feature.sh ./foo.rs
```

## If none of the current minimizers help...

If none of the current minimizers help for your use case, feel free to take inspiration from them, and then contribute your new minimizer back, so as to make future minimization efforts for similar kinds of bugs easier.
