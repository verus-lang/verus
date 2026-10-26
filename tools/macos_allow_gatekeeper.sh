#!/bin/bash
set -e
set -x

script_dir=$(dirname "${BASH_SOURCE[0]}")
cd "$script_dir"

remove_quarantine() {
    local attributes
    attributes=$(xattr "$1")
    if printf '%s\n' "$attributes" | grep -Fxq 'com.apple.quarantine'; then
        xattr -d com.apple.quarantine "$1"
    fi
}

remove_quarantine libverus_builtin.rlib
remove_quarantine libverus_builtin_macros.dylib
remove_quarantine libverus_state_machines_macros.dylib
remove_quarantine rust_verify
remove_quarantine verus
remove_quarantine cargo-verus

remove_quarantine z3
