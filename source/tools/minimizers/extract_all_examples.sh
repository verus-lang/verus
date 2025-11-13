#!/bin/bash
#
# Extract multiple minimal examples from a single input file
# Usage: ./extract_all_examples.sh <input_file>

set -euo pipefail

INPUT="${1:-rb_type_invariant.rs}"
OUTPUT_DIR="examples_extracted"

if [ ! -f "$INPUT" ]; then
    echo "Error: Input file '$INPUT' not found"
    exit 1
fi

echo "╔═══════════════════════════════════════════════════════════════════════╗"
echo "║         Extracting Multiple Examples from: $INPUT"
echo "╚═══════════════════════════════════════════════════════════════════════╝"
echo ""

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Define features to extract
declare -A FEATURES=(
    ["type_invariant"]="type_invariant.*use_type_invariant"
    ["enqueue"]="fn enqueue"
    ["dequeue"]="fn dequeue"
    ["len_method"]="fn len"
    ["spec_functions"]="spec fn"
    ["proof_blocks"]="proof \{"
    ["ensures_clause"]="ensures"
    ["loop_invariant"]="invariant"
    ["view_impl"]="impl.*View"
    ["copy_trait"]="Copy"
)

echo "Will extract examples for these features:"
for feature in "${!FEATURES[@]}"; do
    echo "  • $feature: ${FEATURES[$feature]}"
done
echo ""

# Extract each feature
for feature in "${!FEATURES[@]}"; do
    PATTERN="${FEATURES[$feature]}"
    OUTPUT_FILE="${OUTPUT_DIR}/${feature}_example.rs"
    
    echo "─────────────────────────────────────────────────────────────────────"
    echo "Extracting: $feature"
    echo "Pattern: $PATTERN"
    echo "Output: $OUTPUT_FILE"
    
    # Copy input to foo.rs
    cp "$INPUT" foo.rs
    
    # Check if feature exists in input
    if ! grep -qE "$PATTERN" foo.rs; then
        echo "⊘ Feature not found in input, skipping..."
        echo ""
        continue
    fi
    
    # Run creduce with this feature
    if FEATURE="$PATTERN" timeout 300 creduce --n 4 ./verified_with_feature.sh foo.rs 2>&1 | tail -5; then
        # Copy result
        cp foo.rs "$OUTPUT_FILE"
        LINES=$(wc -l < "$OUTPUT_FILE")
        echo "✓ Extracted! ($LINES lines)"
        
        # Format it
        if [ -x "$(command -v verusfmt)" ]; then
            verusfmt "$OUTPUT_FILE" 2>/dev/null || true
        fi
    else
        echo "⊘ Extraction failed or timed out"
    fi
    echo ""
done

echo "╔═══════════════════════════════════════════════════════════════════════╗"
echo "║                         EXTRACTION COMPLETE                            ║"
echo "╚═══════════════════════════════════════════════════════════════════════╝"
echo ""
echo "Results in: $OUTPUT_DIR/"
ls -lh "$OUTPUT_DIR/" 2>/dev/null | tail -n +2 || echo "No files extracted"
echo ""
echo "Summary:"
for file in "$OUTPUT_DIR"/*.rs; do
    if [ -f "$file" ]; then
        name=$(basename "$file" .rs)
        lines=$(wc -l < "$file")
        echo "  • $name: $lines lines"
    fi
done


