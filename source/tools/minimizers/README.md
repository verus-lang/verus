# Verus Test Case Minimizers

This directory contains automated tools for minimizing Verus code. These tools help you:
- **Create minimal bug reproductions** for reporting issues
- **Extract clean examples** from complex codebases for documentation
- **Isolate specific features** for teaching or demonstration

## Table of Contents

- [What is Code Minimization?](#what-is-code-minimization)
- [How It Works](#how-it-works)
- [Quick Start](#quick-start)
- [Requirements](#requirements)
- [Available Minimizers](#available-minimizers)
- [Usage Examples](#usage-examples)
- [Configuration](#configuration)
- [Troubleshooting](#troubleshooting)
- [Advanced Usage](#advanced-usage)
- [Contributing](#contributing)

---

## What is Code Minimization?

Code minimization automatically reduces source code to the **smallest possible version** that still preserves a specific property you care about.

### Example

**Before (492 lines):** Complex RingBuffer implementation with tests, helpers, and documentation

**After (24 lines):** Minimal example showing just the type invariant feature

**The property preserved:** Code verifies successfully and demonstrates type invariants

### Why Minimize?

1. **Bug Reports**: Smaller reproduction = easier debugging
2. **Documentation**: Minimal examples = clearer teaching
3. **Understanding**: Shows what's essential vs. incidental
4. **Testing**: Creates focused test cases

---

## How It Works

The minimization system has two components:

### 1. C-Reduce (creduce)

The core minimization engine that:
- Systematically removes/simplifies code (functions, statements, expressions, tokens)
- Tests each change to see if it still preserves your property
- Keeps changes that work, reverts those that don't
- Continues until no more reductions are possible

### 2. Interestingness Test Scripts

Bash scripts that define what makes code "interesting" (worth keeping):
- **Exit 0**: Property preserved → keep the change
- **Exit 1**: Property lost → revert the change

**Example:** `verified_with_invariant.sh` checks:
1. Does the code contain `type_invariant`?
2. Does the code contain `use_type_invariant`?
3. Does Verus verify it successfully?

If all three are true → exit 0 (interesting)
If any are false → exit 1 (not interesting)

### The Minimization Process

```
Original file (492 lines)
  ↓ C-Reduce tries: Delete test3()
  ↓ Run: ./verified_with_invariant.sh
  ↓ Result: Still verifies with invariant → Keep change
  
  ↓ C-Reduce tries: Delete helper_fn()
  ↓ Run: ./verified_with_invariant.sh
  ↓ Result: Doesn't verify → Revert change
  
  ↓ C-Reduce tries: Simplify struct field
  ↓ Run: ./verified_with_invariant.sh
  ↓ Result: Still verifies with invariant → Keep change
  
  [... thousands more attempts ...]
  
Final file (24 lines) - cannot be reduced further
```

---

## Quick Start

### Simple Usage (Recommended)

```bash
# 1. Use the helper script
./minimize.sh my_code.rs minimal 8

# 2. Check results
cat foo.rs
```

### Manual Usage

```bash
# 1. Copy your file to foo.rs
cp my_code.rs foo.rs

# 2. Test the interestingness script
./verified_minimal.sh && echo "✓ Works" || echo "✗ Failed"

# 3. Run creduce (8 cores)
creduce --n 8 ./verified_minimal.sh foo.rs

# 4. Check the minimized result
cat foo.rs
verusfmt foo.rs  # Optional: format for readability
```

---

## Requirements

### Installation

1. **C-Reduce**
   ```bash
   sudo apt-get install creduce
   ```
   Or see: https://github.com/csmith-project/creduce/blob/master/INSTALL.md

2. **Verus** (built with `--release` for speed)
   ```bash
   cd /path/to/verus
   ./tools/get-z3.sh && vargo build --release
   ```

3. **Single File** (if your code spans multiple files)
   ```bash
   # Use inline-crate to merge into single file
   cargo install inline-crate
   inline-crate --crate my_crate > single_file.rs
   ```

---

## Available Minimizers

### Error Minimizers (For Bug Reports)

Preserve code that produces specific errors:

| Script | Preserves | Use Case |
|--------|-----------|----------|
| `panicked_in.sh` | Code causing panics | Panic bug reports |
| `rlimit_exceeded.sh` | Code hitting resource limits | Memory/complexity issues |
| `time_exceeded.sh` | Code taking too long | Performance problems |

### Verification Minimizers (For Examples)

Preserve code that **successfully verifies** with specific features:

| Script | Preserves | Use Case |
|--------|-----------|----------|
| `verified_minimal.sh` | Any verified code | Most aggressive: smallest possible |
| `verified_with_invariant.sh` | Type invariant usage | Type invariant examples |
| `verified_with_spec.sh` | Spec functions | Specification examples |
| `verified_with_feature.sh` | Custom pattern (via `FEATURE` env var) | Any feature you specify |

---

## Usage Examples

### Example 1: Minimize a Panic Bug

```bash
# You have code that causes a panic
cp buggy_code.rs foo.rs

# Minimize to smallest reproduction
creduce --n 8 ./panicked_in.sh foo.rs

# Result: Minimal code that still panics
# Submit foo.rs as bug report
```

### Example 2: Extract Type Invariant Example

```bash
# Start with large implementation
cp ring_buffer.rs foo.rs  # 492 lines

# Extract minimal type invariant example
creduce --n 8 ./verified_with_invariant.sh foo.rs

# Result: ~24 lines demonstrating type invariants
verusfmt foo.rs
cp foo.rs docs/examples/type_invariant_simple.rs
```

### Example 3: Extract Specific Feature

```bash
# Extract example showing enqueue method
cp ring_buffer.rs foo.rs
FEATURE="fn enqueue" creduce --n 8 ./verified_with_feature.sh foo.rs

# Extract example with loop invariants
cp ring_buffer.rs foo.rs
FEATURE="loop_invariant" creduce --n 8 ./verified_with_feature.sh foo.rs

# Extract example with proof blocks
cp ring_buffer.rs foo.rs
FEATURE="proof" creduce --n 8 ./verified_with_feature.sh foo.rs
```

### Example 4: Multiple Examples from One File

```bash
mkdir -p examples

# Type invariant
cp original.rs foo.rs
creduce --n 8 ./verified_with_invariant.sh foo.rs
cp foo.rs examples/01_type_invariant.rs

# Spec functions
cp original.rs foo.rs
FEATURE="spec fn" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/02_spec_functions.rs

# Proof blocks
cp original.rs foo.rs
FEATURE="proof \{" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/03_proof_blocks.rs

# Format all
verusfmt examples/*.rs
```

### Example 5: Using the Helper Script

```bash
# Error minimizers
./minimize.sh my_code.rs panic 8
./minimize.sh my_code.rs rlimit 8
./minimize.sh my_code.rs timeout 8

# Verification minimizers
./minimize.sh my_code.rs minimal 8
./minimize.sh my_code.rs invariant 8
./minimize.sh my_code.rs spec 8

# Custom feature
./minimize.sh my_code.rs feature "RingBuffer" 8
```

---

## Configuration

All scripts support environment variables:

### TIMEOUT (default: 30)

Set verification timeout in seconds:

```bash
# Increase timeout for complex verification
TIMEOUT=60 creduce --n 8 ./verified_minimal.sh foo.rs

# Decrease for faster iteration
TIMEOUT=10 creduce --n 8 ./verified_minimal.sh foo.rs
```

### TRACE (default: 0)

Enable bash tracing for debugging:

```bash
# Debug what the script is doing
TRACE=1 ./verified_minimal.sh

# Use with creduce
TRACE=1 creduce --n 8 ./verified_minimal.sh foo.rs
```

### MAX_RUNS (default: 1)

Run verification multiple times (for flaky bugs):

```bash
# For non-deterministic issues
MAX_RUNS=5 ./panicked_in.sh
```

### FEATURE (required for verified_with_feature.sh)

Regex pattern to search for:

```bash
# Simple pattern
FEATURE="enqueue" creduce ./verified_with_feature.sh foo.rs

# Regex pattern
FEATURE="fn enqueue.*ensures" creduce ./verified_with_feature.sh foo.rs
FEATURE="proof.*use_type_invariant" creduce ./verified_with_feature.sh foo.rs
```

---

## Troubleshooting

### Issue: "creduce: command not found"

**Solution:**
```bash
sudo apt-get install creduce
```

### Issue: "Could not find verus binary"

**Solution:**
```bash
# Build Verus first
cd /path/to/verus
./tools/get-z3.sh
vargo build --release
```

### Issue: Minimization takes too long

**Solutions:**
```bash
# Use more cores
creduce --n 16 ./verified_minimal.sh foo.rs

# Increase timeout to avoid retrying slow verifications
TIMEOUT=60 creduce --n 8 ./verified_minimal.sh foo.rs

# Stop and check current progress
# (Ctrl+C, then check foo.rs - it's already reduced)
```

### Issue: C-Reduce gets stuck

**Solutions:**
```bash
# 1. Stop it (Ctrl+C)
# 2. Check current foo.rs - often already well-reduced
# 3. Continue with fewer cores
creduce --n 2 ./verified_minimal.sh foo.rs

# Or try different minimizer
creduce --n 8 ./verified_minimal.sh foo.rs
```

### Issue: Result is too minimal (missing important context)

**Solution:**
```bash
# Use more specific feature pattern
FEATURE="fn enqueue.*ensures" creduce ./verified_with_feature.sh foo.rs

# Or manually add back needed context to the result
```

### Issue: Result doesn't verify (shouldn't happen!)

This indicates a bug in the interestingness test. The test should ensure verification succeeds.

**Workaround:**
```bash
# Enable tracing to debug
TRACE=1 ./verified_minimal.sh

# Check what Verus outputs
./verified_minimal.sh
cat output
```

### Issue: Too many LLVM/compiler errors during minimization

This is normal! C-Reduce tries many invalid transformations. The errors are expected and don't indicate a problem.

### Issue: Interestingness test fails on original file

**Solution:**
```bash
# Test manually first
./verified_minimal.sh && echo "✓ Pass" || echo "✗ Fail"

# If it fails:
# - Check that Verus is built
# - Check that the file verifies: ../../target-verus/release/verus foo.rs
# - For feature tests: ensure file contains the feature
grep "type_invariant" foo.rs
```

---

## Advanced Usage

### Time Estimates

- **<200 lines**: 5-15 minutes
- **200-500 lines**: 15-60 minutes
- **>500 lines**: 1-3 hours

### Parallel Extraction

Extract multiple examples simultaneously:

```bash
# Terminal 1
cp original.rs foo1.rs
FEATURE="enqueue" creduce --n 4 ./verified_with_feature.sh foo1.rs

# Terminal 2
cp original.rs foo2.rs
FEATURE="dequeue" creduce --n 4 ./verified_with_feature.sh foo2.rs
```

### Check Progress Anytime

```bash
# In another terminal while creduce runs
wc -l foo.rs
cat foo.rs
```

### Two-Stage Minimization

First preserve feature, then minimize further:

```bash
# Stage 1: Preserve enqueue
FEATURE="enqueue" creduce --n 8 ./verified_with_feature.sh foo.rs

# Stage 2: Further minimize
creduce --n 8 ./verified_minimal.sh foo.rs
```

### Custom Interestingness Tests

Create your own minimizer:

```bash
#!/bin/bash
# my_custom_test.sh
FILE="${1:-./foo.rs}"
VERUS="../../target-verus/release/verus"

# Your custom conditions
if ! grep -q "MyTrait" "$FILE"; then
  exit 1
fi

timeout 30 "$VERUS" "$FILE" >output 2>&1 || exit 1

if grep -q "verification results::" output && \
   grep "verification results::" output | grep -q "verified"; then
  exit 0
fi

exit 1
```

Then use it:
```bash
chmod +x my_custom_test.sh
creduce --n 8 ./my_custom_test.sh foo.rs
```

---

## Contributing

### Adding New Minimizers

If you create a minimizer for a specific use case, please contribute it back!

1. Create your script (e.g., `verified_with_X.sh`)
2. Follow the pattern of existing scripts
3. Test it thoroughly
4. Add documentation to this README
5. Submit a pull request

### Tips for Writing Interestingness Tests

1. **Be specific**: Check for exact properties you want
2. **Be fast**: Faster tests = faster minimization
3. **Be reliable**: Should never have false positives
4. **Use timeouts**: Prevent hanging on pathological cases
5. **Check verification output carefully**: Look for "verified" AND absence of errors

---

## See Also

- **QUICK_REFERENCE.md** - Cheat sheet for common operations
- **MULTIPLE_EXAMPLES.md** - Detailed guide for extracting multiple examples
- **EXAMPLE_USAGE.md** - Walkthrough of minimizing rb_type_invariant.rs
- **examples/** - Example minimized outputs

---

## Architecture Summary

```
Input File (foo.rs)
        ↓
    C-Reduce
        ↓ (tries transformation)
        ↓
Interestingness Test (e.g., verified_minimal.sh)
        ↓ (runs Verus)
        ↓ (checks output)
        ↓
    Exit 0: Keep     Exit 1: Revert
        ↓                 ↓
    (continue minimizing...)
        ↓
Minimal Output (foo.rs)
```

**Key Insight**: C-Reduce minimizes code size; interestingness tests define what to preserve.

---

## Reduction Logic Deep Dive

### How C-Reduce Works Internally

C-Reduce uses a **multi-pass greedy algorithm** with dozens of transformation passes:

#### Transformation Passes (Examples)

1. **Coarse-Grained Passes** (applied first, faster):
   - `lines` - Delete entire lines
   - `blocks` - Remove code blocks (functions, loops, etc.)
   - `clang_delta` passes - Delete declarations, function parameters, etc.

2. **Fine-Grained Passes** (applied later, slower):
   - `ints` - Simplify integer literals (1000 → 1)
   - `indent` - Remove whitespace
   - `clang_callexpr` - Simplify function calls
   - `replace-array-indexing` - Simplify array accesses
   - Many more specialized transformations...

#### The Algorithm

```python
def creduce(file, interestingness_test, passes):
    current_code = read(file)
    
    while True:
        made_progress = False
        
        # Try each transformation pass in sequence
        for pass_name in passes:
            while True:
                # Try all transformations this pass can make
                transformations = generate_transformations(current_code, pass_name)
                
                found_reduction = False
                for transform in transformations:
                    candidate = apply(transform, current_code)
                    
                    # Key step: test if still interesting
                    if interestingness_test(candidate) == EXIT_SUCCESS:
                        current_code = candidate
                        write(file, current_code)
                        found_reduction = True
                        made_progress = True
                        break  # Start pass over with new code
                
                # Move to next pass when no more reductions found
                if not found_reduction:
                    break
        
        # Stop when no pass can reduce further
        if not made_progress:
            break
    
    return current_code
```

### Concrete Example

Let's trace through minimizing this code:

```rust
// Original: 10 lines
fn main() {
    let x = 100;
    let y = 200;
    println!("Starting");
    if x < y {
        println!("x is less");
        panic!("Error!");
    }
    println!("Done");
}
```

**Goal**: Minimize while preserving panic (interestingness test: `grep "panicked at"`)

**Reduction sequence:**

```
Pass 1 (lines): Try deleting each line
  ✓ Delete line 9 "println!("Done");" → Still panics
  Current: 9 lines

Pass 1 (lines): Try again with 9 lines
  ✓ Delete line 4 "println!("Starting");" → Still panics
  Current: 8 lines

Pass 1 (lines): Try again with 8 lines
  ✗ Delete line 7 "panic!(...)" → Doesn't panic anymore, REVERT
  ✗ Delete line 5 "if x < y {" → Syntax error, REVERT
  ✓ Delete line 2 "let x = 100;" → Wait, now breaks... REVERT
  ✓ Delete line 6 "println!("x is less");" → Still panics
  Current: 7 lines

Pass 1 (lines): Try again with 7 lines
  ✗ No more lines can be deleted → Move to next pass

Pass 2 (blocks): Try deleting blocks
  ✗ Delete if block → Loses panic, REVERT
  No reductions → Move to next pass

Pass 3 (clang_delta): Try simplifying
  [C-specific, mostly skipped for Rust]

Pass 4 (ints): Simplify integers
  ✓ Replace "100" with "1" → Still panics
  ✓ Replace "200" with "2" → Still panics
  Current: 7 lines with simpler values

Pass 5 (indent): Remove whitespace
  ✓ Various whitespace removals
  Current: Still 7 lines, more compact

[More passes...]

No more reductions possible!

Final result: 7 lines
fn main() {
    let x = 1;
    let y = 2;
    if x < y {
        panic!("Error!");
    }
}
```

### What "Minimal" Actually Means

**Important**: C-Reduce finds a **local minimum**, not necessarily a **global minimum**.

#### Local vs Global Minimum

**Local Minimum**: Cannot be reduced further using the available transformations in the available order.

**Global Minimum**: The absolute smallest possible code (might not be reachable).

#### Example of Non-Global Minimum

```rust
// Local minimum (what C-Reduce might find):
fn main() {
    let x = vec![1, 2, 3];
    if x.len() > 0 {
        panic!("Error");
    }
}

// But this is smaller (global minimum):
fn main() {
    panic!("Error");
}
```

Why didn't C-Reduce reach the global minimum? Possible reasons:
1. Deleting the Vec might break parsing before the if-condition is simplified
2. Order of transformations matters - if we simplify Vec first, we might not reach optimal
3. C-Reduce's transformations work conservatively to avoid breaking syntax

### Guarantees and Limitations

#### What C-Reduce Guarantees

✓ **Soundness**: Every intermediate version passes the interestingness test
✓ **Progress**: Each transformation makes the code smaller (fewer tokens/lines)
✓ **Termination**: Algorithm always terminates (finite search space per pass)
✓ **Stability**: Cannot reduce further with available passes

#### What C-Reduce Does NOT Guarantee

✗ **Global optimality**: Might not find the absolute smallest code
✗ **Determinism**: Different runs might produce slightly different results
✗ **Speed**: Can take very long for large files (tries many combinations)
✗ **Readability**: Minimized code often looks strange

### Why Local Minimum is Good Enough

For practical purposes, local minimum is excellent because:

1. **Significant reduction**: Typically reduces 90%+ of code
2. **Property preserved**: Guaranteed to maintain interesting behavior
3. **Reproducible**: Can iterate or use different passes
4. **Predictable**: Terminates in reasonable time

### Improving Minimality

You can get closer to global minimum by:

#### 1. Two-Stage Minimization

```bash
# Stage 1: Keep specific feature
FEATURE="enqueue" creduce --n 8 ./verified_with_feature.sh foo.rs

# Stage 2: Aggressive minimization
creduce --n 8 ./verified_minimal.sh foo.rs
```

#### 2. Different Pass Orders

C-Reduce tries passes in a specific order. Sometimes running multiple times helps:

```bash
# First pass
creduce --n 8 ./verified_minimal.sh foo.rs
cp foo.rs foo_first_pass.rs

# Second pass (might find more reductions)
creduce --n 8 ./verified_minimal.sh foo.rs
```

#### 3. Manual Cleanup + Re-minimize

```bash
# Initial minimization
creduce --n 8 ./verified_minimal.sh foo.rs

# Manual: look at result, manually simplify something obvious
vim foo.rs

# Minimize again
creduce --n 8 ./verified_minimal.sh foo.rs
```

#### 4. Custom Transformations

Write your own pass to handle domain-specific simplifications:

```bash
#!/bin/bash
# custom_simplify.sh - Run before C-Reduce
FILE="$1"

# Your domain-specific simplifications
sed -i 's/very_long_descriptive_name/x/g' "$FILE"
sed -i 's/complex_pattern/simple/g' "$FILE"

# Test if still interesting
./verified_minimal.sh "$FILE"
```

### Parallel Minimization Strategy

C-Reduce parallelizes within each pass, but you can also parallelize across files:

```bash
# 8 cores total, distribute across 2 files
creduce --n 4 ./verified_minimal.sh foo1.rs &
creduce --n 4 ./verified_minimal.sh foo2.rs &
wait
```

### Understanding the Output

After C-Reduce finishes:

```bash
# Check reduction ratio
echo "Original: $(wc -l foo.rs.orig)"
echo "Final: $(wc -l foo.rs)"

# Verify it's still interesting
./verified_minimal.sh && echo "✓ Still passes"

# Try one more manual pass
creduce --n 8 ./verified_minimal.sh foo.rs

# If no more reductions: "pass_lines :: interesting=0"
# This means it's at a local minimum for that pass
```

### Key Takeaway

C-Reduce's "minimal" means:
- **Practically minimal**: Can't be reduced further with known transformations
- **Sound**: Every step maintains the interesting property
- **Good enough**: Achieves 90-99% reduction in most cases

The greedy algorithm with multiple passes ensures a very small result, even if not theoretically optimal.

---

## Quick Reference Commands

```bash
# Most common usage
./minimize.sh my_code.rs minimal 8

# Extract specific features
FEATURE="proof" creduce --n 8 ./verified_with_feature.sh foo.rs

# Minimize bug reproduction
creduce --n 8 ./panicked_in.sh foo.rs

# Format result
verusfmt foo.rs

# Verify result
../../target-verus/release/verus foo.rs

# Check progress during minimization
watch -n 5 'wc -l foo.rs'
```
