#!/usr/bin/env bash

set -eu -o pipefail

[ -n "$VERUS_Z3_PATH" ]
[ -n "$VERUS_SINGULAR_PATH" ]

RUSTC_BOOTSTRAP=1 cargo build -p verus-driver --features singular

verus_sysroot=verus-sysroot

target_dir=target-verus-sysroot

rm -rf $verus_sysroot $target_dir

targets="x86_64-unknown-linux-gnu"

profile=release

for target in $targets; do
    RUSTFLAGS="-C embed-bitcode=yes" \
        cargo run -p cargo-verus -- \
            --target-dir $target_dir \
            --target $target \
            --release \
            -p verus-sysroot-dummy
done

d=$verus_sysroot/lib/rustlib/lib
mkdir -p $d
mv $target_dir/$profile/deps/*.so $d

for target in $targets; do
    d=$verus_sysroot/lib/rustlib/$target/lib
    mkdir -p $d
    mv $target_dir/$target/$profile/deps/* $d
    rm $d/*.d $d/libverus_sysroot_dummy-*.*
done

rm -rf $target_dir
