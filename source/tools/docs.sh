#! /bin/bash

set -e

case $(uname -m) in
  x86_64)
    ARCH=x86_64
    ;;
  arm64)
    ARCH=aarch64
    ;;
  *)
    echo "Unknown architecture $(uname -m)" 1>&2
    exit 1
    ;;
esac

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

cargo build -p verusdoc

echo "Running rustdoc..."
RUSTC_BOOTSTRAP=1 eval ""VERUSDOC=1 VERUS_Z3_PATH="$(pwd)/z3" rustdoc \
  --extern builtin=target-verus/debug/libbuiltin.rlib \
  --extern builtin_macros=target-verus/debug/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros=target-verus/debug/libstate_machines_macros.$DYN_LIB_EXT \
  --edition=2018 \
  --cfg verus_macro_keep_ghost_stubs \
  -Zcrate-attr=feature\\\(stmt_expr_attributes\\\) \
  -Zcrate-attr=feature\\\(negative_impls\\\) \
  -Zcrate-attr=feature\\\(register_tool\\\) \
  -Zcrate-attr=feature\\\(rustc_attrs\\\) \
  -Zcrate-attr=feature\\\(unboxed_closures\\\) \
  -Zcrate-attr=feature\\\(allocator_api\\\) \
  -Zcrate-attr=register_tool\\\(verus\\\) \
  -Zcrate-attr=register_tool\\\(verifier\\\) \
  pervasive/vstd.rs""

echo "Running post-processor..."
./target/debug/verusdoc

echo "Documentation generated at ./doc/vstd/index.html"
