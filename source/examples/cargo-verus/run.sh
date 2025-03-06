#!/usr/bin/env bash

# This script demonstrates the flow enabled by integration with Cargo.
# It requires cargo-verus to be in the current path
# (usually either target-verus/debug or target-verus/release)

# verify an example without codegen (like cargo check) and without applying rustc (like rust_verify
# without --compile)
cargo verus --check --just-verify --manifest-path test/Cargo.toml -p test

# verify an example without codegen (like cargo check)
cargo verus --just-verify --manifest-path test/Cargo.toml -p test

# build and verify an example with codegen (like cargo build)
cargo verus --manifest-path test/Cargo.toml -p test

# this time with an argument for verus
cargo verus --manifest-path test/Cargo.toml -p test -- --verus-arg=--rlimit=60
