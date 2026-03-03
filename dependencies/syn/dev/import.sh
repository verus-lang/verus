#!/bin/bash

if [ ! -f "$1" ]; then
    echo "Usage: dev/import.sh tests/rust/path/to/mod.rs" >&2
    exit 1
fi

set -eu

main=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)/main.rs
echo -n "syn_dev::r#mod! {" > "$main"
cat "$1" >> "$main"
echo "}" >> "$main"
