# Minimizers Quick Reference

## One Example (What You Just Did)

```bash
cp rb_type_invariant.rs foo.rs
creduce --n 8 ./verified_with_invariant.sh foo.rs
# Result: foo.rs (minimal type_invariant example)
```

## Multiple Examples (Extract Different Features)

```bash
mkdir -p examples

# Extract type_invariant example
cp rb_type_invariant.rs foo.rs
creduce --n 8 ./verified_with_invariant.sh foo.rs
cp foo.rs examples/type_invariant.rs

# Extract enqueue example
cp rb_type_invariant.rs foo.rs
FEATURE="fn enqueue" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/enqueue.rs

# Extract dequeue example
cp rb_type_invariant.rs foo.rs
FEATURE="fn dequeue" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/dequeue.rs

# Extract spec function example
cp rb_type_invariant.rs foo.rs
FEATURE="spec fn" creduce --n 8 ./verified_with_spec.sh foo.rs
cp foo.rs examples/spec_functions.rs

# Extract proof block example
cp rb_type_invariant.rs foo.rs
FEATURE="proof" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/proof_blocks.rs
```

## Available Scripts

| Script | What it keeps | Use case |
|--------|---------------|----------|
| `verified_minimal.sh` | Any verified code | Smallest possible |
| `verified_with_invariant.sh` | Type invariants | Invariant examples |
| `verified_with_spec.sh` | Spec functions | Specification examples |
| `verified_with_feature.sh` | Custom pattern (FEATURE env var) | Anything! |

## Common FEATURE Patterns

```bash
# Methods
FEATURE="fn enqueue"
FEATURE="fn dequeue"
FEATURE="fn len"
FEATURE="fn new"

# Traits
FEATURE="impl.*View"
FEATURE="impl.*Copy"

# Verus features
FEATURE="type_invariant"
FEATURE="ensures"
FEATURE="requires"
FEATURE="invariant"        # loop invariants
FEATURE="proof"
FEATURE="spec fn"

# Complex patterns (regex)
FEATURE="fn enqueue.*ensures"
FEATURE="proof.*use_type_invariant"
FEATURE="<T.*Copy>"
```

## Time Management

- Single extraction: ~20-40 minutes
- Use `--n 8` for speed (uses 8 cores)
- Use `--n 2` for parallel extractions (run multiple at once)
- Set TIMEOUT for faster verification: `TIMEOUT=60 creduce ...`

## Format Results

```bash
# Format one file
verusfmt examples/my_example.rs

# Format all examples
verusfmt examples/*.rs
```

## Verify Results

```bash
# Verify one file
../../target-verus/release/verus examples/my_example.rs

# Verify all examples
for f in examples/*.rs; do
    echo "Checking $f..."
    ../../target-verus/release/verus "$f" || echo "FAILED: $f"
done
```

## Clean Up

```bash
# Remove creduce bug reports
rm -rf creduce_bug_*

# Remove intermediate files
rm -f foo.rs.orig output stderr
```

## Full Workflow Example

```bash
#!/bin/bash
# Extract tutorial series from rb_type_invariant.rs

INPUT="rb_type_invariant.rs"
mkdir -p tutorial

# 1. Basic type invariant
cp $INPUT foo.rs
creduce --n 8 ./verified_with_invariant.sh foo.rs
cp foo.rs tutorial/01_type_invariant.rs

# 2. With enqueue
cp $INPUT foo.rs
FEATURE="fn enqueue" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs tutorial/02_enqueue.rs

# 3. With dequeue  
cp $INPUT foo.rs
FEATURE="fn dequeue" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs tutorial/03_dequeue.rs

# Format all
verusfmt tutorial/*.rs

# Verify all
for f in tutorial/*.rs; do
    ../../target-verus/release/verus "$f" || echo "ERROR: $f"
done

echo "Done! Examples in tutorial/"
```

## Tips

1. **Start specific, then generalize**: First extract focused examples (specific methods), then extract broader ones (spec functions)

2. **Use precise patterns**: `FEATURE="fn enqueue"` is better than `FEATURE="enqueue"`

3. **Check intermediate results**: You can Ctrl+C creduce and check `foo.rs` to see current progress

4. **Combine scripts**: First extract with feature, then reduce further with minimal:
   ```bash
   FEATURE="enqueue" creduce ./verified_with_feature.sh foo.rs
   creduce ./verified_minimal.sh foo.rs  # Further reduce
   ```

5. **Parallel extraction** (if you have many cores):
   ```bash
   cp $INPUT foo1.rs && FEATURE="enqueue" creduce --n 2 ./verified_with_feature.sh foo1.rs &
   cp $INPUT foo2.rs && FEATURE="dequeue" creduce --n 2 ./verified_with_feature.sh foo2.rs &
   wait
   ```

## Common Issues

**Problem**: "creduce not found"  
**Solution**: `sudo apt-get install creduce`

**Problem**: Too many LLVM errors  
**Solution**: These are normal for Rust code, not real errors

**Problem**: Takes too long  
**Solution**: Use fewer cores (`--n 2`) or increase timeout (`TIMEOUT=60`)

**Problem**: Result too minimal  
**Solution**: Use more specific FEATURE pattern or manually add back needed context

**Problem**: Result doesn't verify  
**Solution**: This shouldn't happen - the interestingness test checks verification. Report if it does!

## See Also

- `README.md` - Main documentation
- `MULTIPLE_EXAMPLES.md` - Detailed guide for extracting multiple examples
- `EXAMPLE_USAGE.md` - Detailed walkthrough of rb_type_invariant.rs minimization


