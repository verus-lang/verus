#! /bin/bash

VERUS_Z3_PATH="$(pwd)/z3" RUSTC=../rust/install/bin/rustc RUSTDOC=../rust/install/bin/rustdoc ../rust/install/bin/cargo $@
