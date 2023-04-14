#! /bin/bash

set -e

DIR="$( cd "$( dirname $(readlink -f "${BASH_SOURCE[0]}") )" >/dev/null 2>&1 && pwd )"
SOURCE="$DIR/.."

if [ "$(uname)" == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ "$(uname)" == "Linux" ]; then
    DYN_LIB_EXT=so
fi

# default to release, if it is compiled
if [ -e "$SOURCE"/target-verus/release/rust_verify ]; then
    if [ -e "$SOURCE"/target-verus/release/.vstd-fingerprint ] && \
       [ -e "$SOURCE"/target-verus/release/libbuiltin.rlib ] && \
       [ -e "$SOURCE"/target-verus/release/libbuiltin_macros.$DYN_LIB_EXT ] && \
       [ -e "$SOURCE"/target-verus/release/libstate_machines_macros.$DYN_LIB_EXT ] && \
       [ -e "$SOURCE"/target-verus/release/libvstd.rlib ] && \
       [ -e "$SOURCE"/target-verus/release/vstd.vir ] && \
       [ -e "$SOURCE"/target-verus/release/verus-root ]; then
        :
    else
        echo -e "\033[31mwarning (rust-verify.sh): detected a release build, but it appears to be incomplete\033[0m"
    fi
    PROFILE=release
else
    PROFILE=debug
fi

if [ "$1" = "--release" ]; then
    shift
    PROFILE=release
elif [ "$1" = "--debug" ]; then
    shift
    PROFILE=debug
fi

TOOLCHAIN=$(cd "$SOURCE" && rustup show active-toolchain | cut -d ' ' -f 1)

VERUS_Z3_PATH="$SOURCE/z3" rustup run "$TOOLCHAIN" -- "$SOURCE"/target-verus/$PROFILE/rust_verify "$@"
