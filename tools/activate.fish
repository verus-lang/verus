#!/usr/bin/env fish

functions --erase cargo

# Get the script's directory
set SCRIPT_DIR (realpath (dirname (status -f)))

echo "building vargo"
pushd $SCRIPT_DIR/vargo
cargo build --release
popd

set -x PATH $SCRIPT_DIR/vargo/target/release $PATH

function cargo
  echo "when working on Verus do not use cargo directly, use vargo instead" 1>&2
  echo "if you need to, you can still access cargo directly by starting a new shell without running the activate command" 1>&2
  return 1
end
