#!/usr/bin/env bash
# Verifies vstd in the verify-core configuration by building core in the rustlib repo.
set -e
cd /Users/estang/Documents/Verus/rustlib
make core
