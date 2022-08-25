#! /bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
REPO="$DIR/../.."

export VERUS_Z3_PATH="$REPO/source/z3"

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
elif [ "$(uname)" == "Linux" ]; then
    DYN_LIB_EXT=so
fi

cargo run --bin rust_verify -- \
  --pervasive-path "$REPO"/source/pervasive \
  --extern builtin="$REPO"/source/target/debug/libbuiltin.rlib \
  --extern builtin_macros="$REPO"/source/target/debug/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros="$REPO"/source/target/debug/libstate_machines_macros.$DYN_LIB_EXT \
  --sysroot /Users/andreal/.rustup/toolchains/nightly-x86_64-apple-darwin \
  --edition=2018 -Z proc-macro-backtrace "$@"

  # --extern core=/Users/andreal/.rustup/toolchains/nightly-x86_64-apple-darwin/lib/libstd-c047ccf37d2c9989.dylib \
  # --extern std=/Users/andreal/.rustup/toolchains/nightly-x86_64-apple-darwin/lib/libstd-c047ccf37d2c9989.dylib \
