# Extracting Multiple Sub-Examples from One File

## Overview

Instead of getting just ONE minimal example, you can extract MANY different minimal examples from the same input file, each demonstrating a different feature or aspect of your code.

## The Concept

From `rb_type_invariant.rs` (492 lines), you can extract:

| Feature | What it demonstrates | Estimated size |
|---------|---------------------|----------------|
| `type_invariant` | Type invariants | ~20 lines |
| `enqueue` | Queue insertion | ~40 lines |
| `dequeue` | Queue removal | ~40 lines |
| `View trait` | View implementation | ~30 lines |
| `spec fn` | Specification functions | ~15 lines |
| `ensures` | Postconditions | ~25 lines |
| `proof blocks` | Proof code | ~20 lines |
| `loop_invariant` | Loop verification | ~35 lines |

Each example is **independently verified** and **minimal for its feature**.

## How It Works

The `verified_with_feature.sh` script takes a `FEATURE` environment variable with a regex pattern. C-Reduce will:

1. Remove code that doesn't match the pattern
2. Keep removing until only the minimal verified code with that feature remains
3. Result: A focused example of that specific feature

## Method 1: Manual Sequential Extraction

Extract one example at a time:

```bash
cd /home/chuyue/verus/source/tools/minimizers
mkdir -p examples

# Example 1: Type invariant (already done!)
cp foo.rs examples/01_type_invariant.rs

# Example 2: Enqueue method
cp rb_type_invariant.rs foo.rs
FEATURE="fn enqueue" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/02_enqueue.rs

# Example 3: Dequeue method  
cp rb_type_invariant.rs foo.rs
FEATURE="fn dequeue" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/03_dequeue.rs

# Example 4: View trait
cp rb_type_invariant.rs foo.rs
FEATURE="impl.*View" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/04_view_trait.rs

# Example 5: Spec functions
cp rb_type_invariant.rs foo.rs
FEATURE="spec fn" creduce --n 8 ./verified_with_spec.sh foo.rs
cp foo.rs examples/05_spec_functions.rs

# Example 6: Loop invariants
cp rb_type_invariant.rs foo.rs
FEATURE="invariant" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/06_loop_invariant.rs

# Example 7: Ensures clauses
cp rb_type_invariant.rs foo.rs
FEATURE="ensures" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/07_ensures.rs

# Example 8: Proof blocks
cp rb_type_invariant.rs foo.rs
FEATURE="proof" creduce --n 8 ./verified_with_feature.sh foo.rs
cp foo.rs examples/08_proof.rs
```

## Method 2: Automated Batch Extraction

Use the automated script:

```bash
./extract_all_examples.sh rb_type_invariant.rs
```

This will extract all common features automatically.

**Note:** This takes time! Each extraction is 20-40 minutes, so extracting 10 examples could take 3-6 hours. Consider:
- Running overnight
- Using fewer cores per extraction (`--n 2`) but running multiple in parallel
- Extracting only the features you need

## Method 3: Parallel Extraction

Extract multiple examples simultaneously (if you have many cores):

```bash
# Terminal 1
cp rb_type_invariant.rs foo1.rs
FEATURE="fn enqueue" creduce --n 2 ./verified_with_feature.sh foo1.rs &

# Terminal 2  
cp rb_type_invariant.rs foo2.rs
FEATURE="fn dequeue" creduce --n 2 ./verified_with_feature.sh foo2.rs &

# Terminal 3
cp rb_type_invariant.rs foo3.rs
FEATURE="impl.*View" creduce --n 2 ./verified_with_feature.sh foo3.rs &

# Wait for all to complete
wait
```

## Advanced: Custom Feature Extraction

Extract examples for very specific patterns:

```bash
# Extract example with saturating_sub
FEATURE="saturating_sub" creduce --n 8 ./verified_with_feature.sh foo.rs

# Extract example with modulo operations
FEATURE="% [a-z]" creduce --n 8 ./verified_with_feature.sh foo.rs

# Extract example with specific struct fields
FEATURE="head.*tail" creduce --n 8 ./verified_with_feature.sh foo.rs

# Extract example with generic type parameters
FEATURE="<T.*Copy>" creduce --n 8 ./verified_with_feature.sh foo.rs
```

## Use Cases

### 1. Creating Tutorial Series

Extract examples progressively showing different concepts:
- `01_basic_struct.rs` - Simple struct
- `02_with_spec.rs` - Adding specifications
- `03_with_proof.rs` - Adding proofs
- `04_with_invariant.rs` - Adding invariants
- `05_complete.rs` - Full implementation

### 2. Documentation Examples

Create focused examples for each Verus feature in your documentation.

### 3. Teaching Materials

Extract examples of increasing complexity for students:
- Beginner: Simple ensures/requires
- Intermediate: Spec functions and proofs
- Advanced: Type invariants and complex loops

### 4. Bug Report Collection

Extract minimal examples showing different edge cases or bugs.

### 5. Benchmark Suite

Create a suite of minimal verified examples for performance testing.

## Tips

1. **Start with the most specific features first** - Generic features (like "spec fn") might match too much

2. **Use precise regex patterns** - Better patterns lead to better results:
   - Good: `fn enqueue.*ensures`
   - Better: `fn enqueue.*\(.*\).*ensures`

3. **Combine with minimal script** - For even smaller examples:
   ```bash
   FEATURE="enqueue" creduce ./verified_with_feature.sh foo.rs
   # Then further reduce without feature requirement
   creduce ./verified_minimal.sh foo.rs
   ```

4. **Check results** - Always verify the extracted example:
   ```bash
   ../../target-verus/release/verus examples/my_example.rs
   ```

5. **Format for readability**:
   ```bash
   verusfmt examples/*.rs
   ```

## Example Workflow

Complete workflow for creating a tutorial series:

```bash
#!/bin/bash
# Create a series of examples from rb_type_invariant.rs

INPUT="rb_type_invariant.rs"
OUTPUT_DIR="tutorial_examples"
mkdir -p "$OUTPUT_DIR"

# Define features in order of complexity
declare -a FEATURES=(
    "struct RingBuffer:01_struct"
    "spec fn:02_spec_function"  
    "ensures:03_ensures"
    "proof:04_proof_block"
    "type_invariant:05_type_invariant"
    "fn enqueue:06_enqueue"
    "fn dequeue:07_dequeue"
    "invariant:08_loop_invariant"
)

for entry in "${FEATURES[@]}"; do
    PATTERN="${entry%%:*}"
    NAME="${entry##*:}"
    
    echo "Extracting: $NAME (pattern: $PATTERN)"
    cp "$INPUT" foo.rs
    FEATURE="$PATTERN" creduce --n 8 ./verified_with_feature.sh foo.rs
    cp foo.rs "$OUTPUT_DIR/${NAME}.rs"
    verusfmt "$OUTPUT_DIR/${NAME}.rs"
done

echo "Complete! Examples in $OUTPUT_DIR/"
```

## Limitations

1. **Time consuming** - Each extraction takes 20-40 minutes
2. **Not deterministic** - Results may vary slightly between runs
3. **May be too minimal** - Sometimes strips too much context
4. **Requires verification** - Only works if code still verifies after reduction

## Solutions to Limitations

- **Too minimal?** Use `verified_minimal.sh` first, then manually add back needed context
- **Too slow?** Run extractions in parallel, or use `--n` with fewer cores
- **Want more control?** Edit the interestingness test scripts to require specific elements

## Going Further

### Create Custom Extractors

You can create specialized interestingness tests:

```bash
# verified_with_ringbuffer.sh
# Keeps RingBuffer AND type_invariant

#!/bin/bash
FILE="${1:-./foo.rs}"
# ... (similar to verified_with_feature.sh)

# Check for both features
if ! grep -q "RingBuffer" "$FILE"; then exit 1; fi
if ! grep -q "type_invariant" "$FILE"; then exit 1; fi

# Verify
timeout 30 ../../target-verus/release/verus "$FILE" >output 2>&1 || exit 1
grep -q "verified" output && ! grep -E "[1-9][0-9]* errors" output
```

Then use it:
```bash
creduce ./verified_with_ringbuffer.sh foo.rs
```

## Summary

**You can extract as many sub-examples as you want!** Each run of creduce with a different `FEATURE` pattern will give you a different minimal example focusing on that feature. This is perfect for creating tutorial series, documentation, or understanding different aspects of complex code.


