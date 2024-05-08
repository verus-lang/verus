#! /bin/bash

. /root/.cargo/env

export VERUS_SINGULAR_PATH=/usr/bin/Singular

# cargo run --release -- $@
cargo run -- $@