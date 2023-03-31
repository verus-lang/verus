#! /bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SOURCE="$DIR/.."

TOOLCHAIN=`rustup show active-toolchain | cut -d ' ' -f 1`

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

export VERUS_Z3_PATH="$SOURCE/z3"

rustup run $TOOLCHAIN -- "$SOURCE"/target/debug/rust_verify \
        --edition=2018 \
        --extern builtin="$SOURCE"/target/debug/libbuiltin.rlib \
        --extern builtin_macros="$SOURCE"/target/debug/libbuiltin_macros.$DYN_LIB_EXT \
        --extern state_machines_macros="$SOURCE"/target/debug/libstate_machines_macros.$DYN_LIB_EXT \
        --import vstd="$SOURCE"/target/debug/vstd.vir \
        --extern vstd="$SOURCE"/target/debug/libvstd.rlib \
        "$@"
