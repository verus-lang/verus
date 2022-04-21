#! /bin/bash

color_blue="\x1B[1;94m"
color_reset="\x1B[0m"

if [ "$#" -ne 1 ]; then
    echo "$0" >&2
    echo "  build on *nix, run the verifier on a single file with logging of air, vir, and smt to files in 'log/' in the same dire as the file" >&2
    echo "usage: $0 <file>" >&2
    exit -1
fi

rs_file=$1
rs_file_dir=`dirname "$rs_file"`
rs_file_basename=`basename "$rs_file"`

mkdir -p $rs_file_dir/log

RUSTC=../rust/install/bin/rustc ../rust/install/bin/cargo build && \
        ./tools/rust-verify.sh $rs_file \
        --log-dir $rs_file_dir/log --log-all
result=$?

echo
echo -e "${color_blue}logs${color_reset}" "$rs_file_dir/log"
exit $?
