# Example: Minimizing rb_type_invariant.rs

This example shows how to extract a minimal verified example from `rb_type_invariant.rs` that demonstrates type invariants.

## Quick Start

```bash
cd /home/chuyue/verus/source/tools/minimizers

# 1. File is already here as foo.rs (492 lines)
cp rb_type_invariant.rs foo.rs

# 2. Test the interestingness script
./verified_with_invariant.sh && echo "✓ Works"

# 3. Run creduce (8 cores)
creduce --n 8 ./verified_with_invariant.sh ./foo.rs

# 4. Check results
wc -l foo.rs
cat foo.rs
```

## What Gets Minimized

**Before (492 lines):**
- RingBuffer struct with View impl
- Helper functions (saturating_sub, mod_auto, etc.)
- Full RingBuffer implementation (new, enqueue, dequeue, etc.)
- 4 test functions (test1, test2, test3, test4)
- All the assertions and proof blocks

**After (estimated ~50-150 lines):**
- Minimal RingBuffer struct
- Type invariant definition
- One or two methods that use `use_type_invariant()`
- Essential spec functions
- No test functions (or minimal test)

## Alternative Approaches

### Keep More Features

If you want to keep specific things, use `verified_with_feature.sh`:

```bash
# Keep RingBuffer in the result
FEATURE="RingBuffer" creduce --n 8 ./verified_with_feature.sh ./foo.rs

# Keep enqueue method specifically
FEATURE="fn enqueue" creduce --n 8 ./verified_with_feature.sh ./foo.rs

# Keep loop-related code
FEATURE="loop|invariant" creduce --n 8 ./verified_with_feature.sh ./foo.rs
```

### Most Aggressive Reduction

For the absolute smallest verified example:

```bash
creduce --n 8 ./verified_minimal.sh ./foo.rs
```

This might remove type_invariant features entirely, keeping only the simplest verification.

## Troubleshooting

### Timeout Issues

If verification takes too long:

```bash
TIMEOUT=60 creduce --n 8 ./verified_with_invariant.sh ./foo.rs
```

### Debug Script Issues

Enable tracing:

```bash
TRACE=1 ./verified_with_invariant.sh
```

### C-Reduce Gets Stuck

Sometimes C-Reduce can get stuck. You can:
1. Stop it (Ctrl+C)
2. Check current `foo.rs` - it's usually already quite reduced
3. Continue with fewer cores: `creduce --n 2 ./verified_with_invariant.sh ./foo.rs`

## Expected Timeline

- **Small files (<200 lines):** 5-15 minutes
- **Medium files (200-500 lines):** 15-60 minutes  
- **Large files (>500 lines):** 1-3 hours

The current `rb_type_invariant.rs` (492 lines) should take about 20-40 minutes with 8 cores.

## Real-World Use Cases

1. **Creating Documentation Examples**
   ```bash
   # Extract minimal type_invariant example for docs
   creduce ./verified_with_invariant.sh ./foo.rs
   cp foo.rs ../../../docs/examples/type_invariant_simple.rs
   ```

2. **Bug Reports**
   ```bash
   # Minimize code that exposes a bug
   creduce ./rlimit_exceeded.sh ./foo.rs
   # Submit foo.rs as minimal reproduction
   ```

3. **Tutorial Generation**
   ```bash
   # Extract examples showing different features
   FEATURE="spec fn" creduce ./verified_with_feature.sh ./foo.rs
   mv foo.rs tutorial_spec_example.rs
   
   FEATURE="proof \{" creduce ./verified_with_feature.sh ./foo.rs  
   mv foo.rs tutorial_proof_example.rs
   ```

## Next Steps

After getting your minimized example:

1. **Format it:** `verusfmt foo.rs`
2. **Verify it:** `../../target-verus/release/verus foo.rs`
3. **Review it:** Make sure it still demonstrates what you wanted
4. **Adjust if needed:** You can manually tweak the minimized code


