#! /bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
REPO="$DIR/../.."

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

if [ "$(uname)" == "Darwin" ]; then
    DYN_LIB_EXT=dylib
    export DYLD_LIBRARY_PATH="$REPO/rust/install/lib/rustlib/${ARCH}-apple-darwin/lib"
elif [ "$(uname)" == "Linux" ]; then
    DYN_LIB_EXT=so
    export LD_LIBRARY_PATH="$REPO/rust/install/lib/rustlib/${ARCH}-unknown-linux-gnu/lib"
fi

export VERUS_Z3_PATH="$REPO/source/z3"

"$REPO"/rust/install/bin/rust_verify \
  --pervasive-path "$REPO"/source/pervasive \
  --extern builtin="$REPO"/rust/install/bin/libbuiltin.rlib \
  --extern builtin_macros="$REPO"/rust/install/bin/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros="$REPO"/rust/install/bin/libstate_machines_macros.$DYN_LIB_EXT \
  --edition=2018 -Z proc-macro-backtrace "$@"
