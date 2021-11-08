#! /bin/bash

RUST_INSTALL_PATH=/home/yizhou7/rust/install
DUST_Z3_PATH="./tools/z3" DYLD_LIBRARY_PATH="{$RUST_INSTALL_PATH}/lib/rustlib/x86_64-apple-darwin/lib" LD_LIBRARY_PATH="{$RUST_INSTALL_PATH}/lib" $RUST_INSTALL_PATH/bin/rust_verify -L {$RUST_INSTALL_PATH}/bin $@
