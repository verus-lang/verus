#! /bin/bash

DUST_Z3_PATH="$(pwd)/z3" RUSTC=../install/bin/rustc RUSTDOC=../install/bin/rustdoc ../install/bin/cargo $@
