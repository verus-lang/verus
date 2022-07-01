#! /bin/bash

VERUSDOC=1 VERUS_Z3_PATH=/Users/thance/verus/source/z3 DYLD_LIBRARY_PATH=../rust/install/lib/rustlib/x86_64-apple-darwin/lib LD_LIBRARY_PATH=../rust/install/lib/rustlib/x86_64-unknown-linux-gnu/lib ../rust/install/bin/rustdoc --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/libbuiltin_macros.dylib --extern state_machines_macros=../rust/install/bin/libstate_machines_macros.dylib --edition=2018 -Zenable_feature=stmt_expr_attributes -Zenable_feature=box_syntax -Zenable_feature=box_patterns -Zenable_feature=negative_impls ./lib.rs

./target/debug/verusdoc
