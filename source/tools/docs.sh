#! /bin/bash

set -e

RUSTDOC=""
if [ "x$1" = "x--strict" ]; then
    RUSTDOC="-D warnings"
fi

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

. ../tools/activate
vargo build -p verusdoc
vargo build --vstd-no-verify

echo "Running rustdoc..."
RUSTC_BOOTSTRAP=1 eval ""VERUSDOC=1 VSTD_KIND=IsVstd VERUS_Z3_PATH="$(pwd)/z3"  rustdoc \
  --extern verus_builtin=target-verus/debug/libverus_builtin.rlib \
  --extern verus_builtin_macros=target-verus/debug/libverus_builtin_macros.$DYN_LIB_EXT \
  --extern verus_state_machines_macros=target-verus/debug/libverus_state_machines_macros.$DYN_LIB_EXT \
  --edition=2018 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature=\"std\"' \
  --cfg 'feature=\"alloc\"' \
  -Zcrate-attr=feature\\\(stmt_expr_attributes\\\) \
  -Zcrate-attr=feature\\\(negative_impls\\\) \
  -Zcrate-attr=feature\\\(register_tool\\\) \
  -Zcrate-attr=feature\\\(rustc_attrs\\\) \
  -Zcrate-attr=feature\\\(unboxed_closures\\\) \
  -Zcrate-attr=feature\\\(custom_inner_attributes\\\) \
  -Zcrate-attr=register_tool\\\(verus\\\) \
  -Zcrate-attr=register_tool\\\(verifier\\\) \
  -Zcrate-attr=register_tool\\\(verusfmt\\\) \
  -Zcrate-attr=allow\\\(internal_features\\\) \
  -Zcrate-attr=allow\\\(unused_braces\\\) \
  -Zproc-macro-backtrace \
  $RUSTDOC \
  vstd/vstd.rs""

echo "Running post-processor..."
./target/debug/verusdoc

echo "Documentation generated at ./doc/vstd/index.html"
