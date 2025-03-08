#!/usr/bin/env bash

# This script demonstrates the flow enabled by integration with Cargo.
# It requires cargo-verus to be in the current path
# (usually either target-verus/debug or target-verus/release)

# verify an example without codegen (like cargo check) and without applying rustc (like rust_verify
# without --compile)
cargo verus check --manifest-path test/Cargo.toml -p test

# verify an example without codegen (like cargo check)
cargo verus verify --manifest-path test/Cargo.toml -p test

# build and verify an example with codegen (like cargo build)
cargo verus build --manifest-path test/Cargo.toml -p test

# clean with regular cargo
cargo clean --manifest-path test/Cargo.toml

# this time with an argument for verus
cargo verus build --manifest-path test/Cargo.toml -p test -- --rlimit=60
