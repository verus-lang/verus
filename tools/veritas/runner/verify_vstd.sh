set -e
set -x

unset RUSTUP_TOOLCHAIN
cd source

. ../tools/activate

vargo run -p rust_verify -- \
    --internal-test-mode \
    --extern builtin=target/debug/libbuiltin.rlib \
    --extern builtin_macros=target/debug/libbuiltin_macros.dylib \
    --extern state_machines_macros=target/debug/libstate_machine_macros.rlib \
    --no-vstd \
    --crate-type=lib \
    --output-json \
    --time-expanded \
    vstd/vstd.rs
