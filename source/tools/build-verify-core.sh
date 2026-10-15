#!/usr/bin/env bash
set -e
cd "$(dirname "$0")/.."
source ../tools/activate
vargo build --release --vstd-no-std --vstd-no-alloc -- --verus-verify-core
