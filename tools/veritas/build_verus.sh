set -e
set -x

unset RUSTUP_TOOLCHAIN
cd source

# TODO restore once line_count is fixed
# pushd tools/line_count
# cargo build --release
# popd

. ../tools/activate
# ./tools/get-z3.sh
echo $RUSTUP_TOOLCHAIN
vargo build --release $VERUS_FEATURES_ARGS
