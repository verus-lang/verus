#!/bin/bash
#
# Interestingness test: keeps code that verifies AND uses a specific feature
# Usage: FEATURE="proof" ./verified_with_feature.sh foo.rs
# Or:    FEATURE="exec.*ensures" ./verified_with_feature.sh foo.rs (regex supported)

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

# Configuration
FILE="${1:-./foo.rs}"
FEATURE="${FEATURE:-proof}"
TIMEOUT="${TIMEOUT:-30}"
TRACE="${TRACE:-0}"

set -euo pipefail
if [ "$TRACE" = "1" ]; then
  set -x
fi

# Find Verus binary
if [ -x "${DIR}/../../target-verus/release/verus" ]; then
  VERIFY="${DIR}/../../target-verus/release/verus"
elif [ -x "${DIR}/../../target-verus/debug/verus" ]; then
  VERIFY="${DIR}/../../target-verus/debug/verus"
else
  echo >&2 "Error: Could not find verus binary"
  exit 1
fi

# Check that the file contains the feature
if ! grep -E "$FEATURE" "$FILE" >/dev/null; then
  exit 1
fi

# Run verification and check for success
timeout "$TIMEOUT" "$VERIFY" "$FILE" >output 2>&1 || exit 1

# Check that verification succeeded
if grep -q "verification results::" output && \
   grep "verification results::" output | grep -q "verified" && \
   ! grep -E "[1-9][0-9]* errors" output; then
  exit 0
fi

exit 1
