#!/usr/bin/env fish

functions --erase cargo

# Get the script's directory
set SCRIPT_DIR (realpath (dirname (status -f)))

echo "building vargo"
pushd $SCRIPT_DIR/vargo
cargo build --release
popd

set -x PATH $SCRIPT_DIR/vargo/target/release $PATH

echo "WARNING: Vargo is being deprecated. Use Cargo instead. Refer to `BUILD.md`."
echo "  See also: https://github.com/verus-lang/verus/pull/2686"

function cargo
  echo "when working on Verus do not use cargo directly, use vargo instead" 1>&2
  echo "if you need to, you can still access cargo directly by starting a new shell without running the activate command" 1>&2
  return 1
end
