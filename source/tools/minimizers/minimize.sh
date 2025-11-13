#!/bin/bash
#
# Helper script to simplify the minimization process
# Usage: ./minimize.sh <input_file> <minimizer_type> [cores]

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

function usage() {
  cat << EOF
Usage: $0 <input_file> <minimizer_type> [cores]

Minimizer Types:
  error:
    panic              - Minimizes code that panics
    rlimit             - Minimizes code hitting resource limits
    timeout            - Minimizes code taking too long
  
  verified:
    minimal            - Most aggressive: any verified code
    invariant          - Keeps type_invariant usage
    spec               - Keeps spec functions
    feature PATTERN    - Keeps custom feature (e.g., "RingBuffer")

Arguments:
  input_file         - Path to .rs file to minimize
  minimizer_type     - One of the types above
  cores              - Number of cores to use (default: 4)

Examples:
  $0 my_code.rs panic
  $0 my_code.rs invariant 8
  $0 my_code.rs feature "RingBuffer" 4

Environment Variables:
  TIMEOUT=30         - Verification timeout in seconds
  TRACE=1            - Enable debug tracing
EOF
  exit 1
}

# Parse arguments
if [ $# -lt 2 ]; then
  usage
fi

INPUT_FILE="$1"
MINIMIZER_TYPE="$2"
CORES="${3:-4}"
FEATURE_PATTERN=""

# Handle feature pattern
if [ "$MINIMIZER_TYPE" = "feature" ]; then
  if [ $# -lt 3 ]; then
    echo -e "${RED}Error: 'feature' minimizer requires a pattern${NC}"
    usage
  fi
  FEATURE_PATTERN="$3"
  CORES="${4:-4}"
fi

# Validate input file
if [ ! -f "$INPUT_FILE" ]; then
  echo -e "${RED}Error: Input file '$INPUT_FILE' not found${NC}"
  exit 1
fi

# Check for creduce
if ! command -v creduce &> /dev/null; then
  echo -e "${RED}Error: creduce is not installed${NC}"
  echo -e "${YELLOW}Install with: sudo apt-get install creduce${NC}"
  exit 1
fi

# Map minimizer type to script
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
case "$MINIMIZER_TYPE" in
  panic)
    SCRIPT="${DIR}/panicked_in.sh"
    ;;
  rlimit)
    SCRIPT="${DIR}/rlimit_exceeded.sh"
    ;;
  timeout)
    SCRIPT="${DIR}/time_exceeded.sh"
    ;;
  minimal)
    SCRIPT="${DIR}/verified_minimal.sh"
    ;;
  invariant)
    SCRIPT="${DIR}/verified_with_invariant.sh"
    ;;
  spec)
    SCRIPT="${DIR}/verified_with_spec.sh"
    ;;
  feature)
    SCRIPT="${DIR}/verified_with_feature.sh"
    export FEATURE="$FEATURE_PATTERN"
    ;;
  *)
    echo -e "${RED}Error: Unknown minimizer type '$MINIMIZER_TYPE'${NC}"
    usage
    ;;
esac

# Verify script exists
if [ ! -x "$SCRIPT" ]; then
  echo -e "${RED}Error: Script '$SCRIPT' not found or not executable${NC}"
  exit 1
fi

# Copy to foo.rs
cp "$INPUT_FILE" "${DIR}/foo.rs"
ORIGINAL_LINES=$(wc -l < "${DIR}/foo.rs")

echo -e "${BLUE}╔═══════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║           Verus Code Minimizer                        ║${NC}"
echo -e "${BLUE}╚═══════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "${GREEN}Input file:${NC}      $INPUT_FILE"
echo -e "${GREEN}Lines:${NC}           $ORIGINAL_LINES"
echo -e "${GREEN}Minimizer:${NC}       $MINIMIZER_TYPE"
if [ -n "$FEATURE_PATTERN" ]; then
  echo -e "${GREEN}Feature:${NC}         $FEATURE_PATTERN"
fi
echo -e "${GREEN}Cores:${NC}           $CORES"
echo -e "${GREEN}Script:${NC}          $(basename "$SCRIPT")"
echo ""

# Test interestingness script
echo -e "${YELLOW}Testing interestingness script...${NC}"
cd "${DIR}"
if ! "$SCRIPT"; then
  echo -e "${RED}✗ Interestingness test failed!${NC}"
  echo -e "${RED}The file doesn't match the minimizer criteria.${NC}"
  echo ""
  echo "Possible reasons:"
  echo "  - File doesn't produce the expected error (for error minimizers)"
  echo "  - File doesn't verify (for verified minimizers)"
  echo "  - File doesn't contain required feature (for feature minimizers)"
  exit 1
fi
echo -e "${GREEN}✓ Interestingness test passed!${NC}"
echo ""

# Show what will be preserved
echo -e "${YELLOW}C-Reduce will preserve:${NC}"
case "$MINIMIZER_TYPE" in
  panic)
    echo "  • Code that causes panics"
    ;;
  rlimit)
    echo "  • Code that exceeds resource limits"
    ;;
  timeout)
    echo "  • Code that takes too long to verify"
    ;;
  minimal)
    echo "  • Any code that successfully verifies"
    ;;
  invariant)
    echo "  • Code with type_invariant"
    echo "  • Code with use_type_invariant calls"
    ;;
  spec)
    echo "  • Code with spec functions"
    ;;
  feature)
    echo "  • Code matching pattern: $FEATURE_PATTERN"
    ;;
esac
echo ""

# Estimate time
if [ "$ORIGINAL_LINES" -lt 200 ]; then
  TIME_EST="5-15 minutes"
elif [ "$ORIGINAL_LINES" -lt 500 ]; then
  TIME_EST="15-60 minutes"
else
  TIME_EST="1-3 hours"
fi
echo -e "${YELLOW}Estimated time:${NC} $TIME_EST"
echo ""

# Run creduce
echo -e "${GREEN}Starting C-Reduce...${NC}"
echo -e "${BLUE}(You can check foo.rs at any time to see progress)${NC}"
echo ""

if ! creduce --n "$CORES" "$SCRIPT" foo.rs; then
  echo -e "${RED}C-Reduce failed or was interrupted${NC}"
  exit 1
fi

# Show results
FINAL_LINES=$(wc -l < foo.rs)
REDUCTION=$((100 - (FINAL_LINES * 100 / ORIGINAL_LINES)))

echo ""
echo -e "${GREEN}╔═══════════════════════════════════════════════════════╗${NC}"
echo -e "${GREEN}║           Minimization Complete!                      ║${NC}"
echo -e "${GREEN}╚═══════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "${GREEN}Original:${NC}   $ORIGINAL_LINES lines"
echo -e "${GREEN}Reduced:${NC}    $FINAL_LINES lines"
echo -e "${GREEN}Savings:${NC}    ${REDUCTION}%"
echo ""
echo -e "${YELLOW}Next steps:${NC}"
echo "  1. Review: cat foo.rs"
echo "  2. Format: verusfmt foo.rs"
echo "  3. Verify: ../../target-verus/release/verus foo.rs"
echo "  4. Copy to desired location"
echo ""


