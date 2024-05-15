#! /bin/bash

if [ "$(dirname "$0")" != "." ]; then
    echo "Please run the script from its directory."
    exit 1
fi

docker run \
    -v verus-veritas-repo-cache:/root/repos-cache \
    -v $(pwd):/root/veritas \
    -v /root/work \
    -v verus-veritas-cargo-cache:/root/.cargo \
    -v verus-veritas-z3-cache:/root/z3-cache \
    -v verus-veritas-rustup:/root/.rustup \
    -v $(pwd)/output:/root/output \
    --rm veritas:rust-1.76.0 $@
