#! /bin/bash

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

if [ `uname -m` == "arm64" ]; then
    ARCH_DIR=aarch64-apple-darwin
else
    ARCH_DIR=x86_x64-apple-darwin
fi

VERUS_Z3_PATH="$(pwd)/z3" DYLD_LIBRARY_PATH=../rust/install/lib/rustlib/$ARCH_DIR/lib LD_LIBRARY_PATH=../rust/install/lib/rustlib/x86_64-unknown-linux-gnu/lib ../rust/install/bin/rust_verify --pervasive-path pervasive --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/libbuiltin_macros.$DYN_LIB_EXT --extern state_machines_macros=../rust/install/bin/libstate_machines_macros.$DYN_LIB_EXT --edition=2018 $@
