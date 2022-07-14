#! /bin/bash

TEMPD=$(mktemp -d)

cp -r pervasive $TEMPD
echo "#[allow(rustdoc::invalid_rust_codeblocks)] pub mod pervasive;" >> $TEMPD/lib.rs

echo "Running rustdoc..."
VERUSDOC=1 VERUS_Z3_PATH=/Users/thance/verus/source/z3 DYLD_LIBRARY_PATH=../rust/install/lib/rustlib/x86_64-apple-darwin/lib LD_LIBRARY_PATH=../rust/install/lib/rustlib/x86_64-unknown-linux-gnu/lib ../rust/install/bin/rustdoc --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/libbuiltin_macros.dylib --extern state_machines_macros=../rust/install/bin/libstate_machines_macros.dylib --edition=2018 -Zenable_feature=stmt_expr_attributes -Zenable_feature=box_syntax -Zenable_feature=box_patterns -Zenable_feature=negative_impls $TEMPD/lib.rs

rm -rf $TEMPD

echo "Running post-processor..."
./target/debug/verusdoc

echo "Documentation generated at ./doc/lib/index.html"
