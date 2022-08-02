#! /bin/bash

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
    LIB_PATH="DYLD_LIBRARY_PATH=$(pwd)/../rust/install/lib/rustlib/${ARCH}-apple-darwin/lib"
elif [ `uname` == "Linux" ]; then
    LIB_PATH="LD_LIBRARY_PATH=$(pwd)/../rust/install/lib/rustlib/${ARCH}-unknown-linux-gnu/lib"
fi

eval ""VERUS_Z3_PATH="$(pwd)/z3" $LIB_PATH RUSTC=../rust/install/bin/rustc RUSTDOC=../rust/install/bin/rustdoc ../rust/install/bin/cargo $@""
