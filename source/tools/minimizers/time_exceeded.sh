#! /bin/bash

set -eo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
VERIFY="${DIR}/../rust-verify.sh"

timeout 10 "${VERIFY}" ./foo.rs 2>stderr >/dev/null || true

if grep 'has been running for' stderr >/dev/null; then
    exit 0
else
    exit 1
fi
