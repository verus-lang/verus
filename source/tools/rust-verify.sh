#! /bin/bash

if [ "$1" = "--release" ]; then
    shift
    PROFILE=release
else
    PROFILE=debug
fi

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SOURCE="$DIR/.."

TOOLCHAIN=`rustup show active-toolchain | cut -d ' ' -f 1`

VERUS_Z3_PATH='./z3' VERUS_ROOT=target-verus/$PROFILE \
        rustup run $TOOLCHAIN -- ./target-verus/$PROFILE/rust_verify \
        "$@"
