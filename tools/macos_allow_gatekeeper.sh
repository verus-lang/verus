#!/bin/bash
set -e
set -x

cd "$( dirname "${{BASH_SOURCE[0]}}" )"

xattr -d com.apple.quarantine libverus_builtin.rlib
xattr -d com.apple.quarantine libverus_builtin_macros.dylib
xattr -d com.apple.quarantine libverus_state_machines_macros.dylib
xattr -d com.apple.quarantine rust_verify
xattr -d com.apple.quarantine verus
xattr -d com.apple.quarantine cargo-verus

xattr -d com.apple.quarantine z3
