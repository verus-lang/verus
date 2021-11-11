#! /bin/bash

VERUS_Z3_PATH="$(pwd)/z3" DYLD_LIBRARY_PATH=../rust/install/lib/rustlib/x86_64-apple-darwin/lib LD_LIBRARY_PATH=../rust/install/lib ../rust/install/bin/rust_verify -L ../rust/install/bin $@
