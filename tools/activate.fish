#!/usr/bin/env fish

# Get the script's directory
set SCRIPT_DIR (realpath (dirname (status -f)))

echo "building vargo"
pushd $SCRIPT_DIR/vargo
cargo build --release
popd

set -x PATH $SCRIPT_DIR/vargo/target/release $PATH