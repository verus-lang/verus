#!/usr/bin/env bash
# Recompile vstd after changing the macro or TSM resource modules.
# Verify the new modules; this does not run the Verus test suite.
set -euo pipefail

example_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd "$example_dir/../.." && pwd)"
verifier="${VERUS_BIN:-$repo_dir/source/target-verus/release/verus}"
artifact_dir="$(cd "$(dirname "$verifier")" && pwd)"
extension=so
if [[ "$(uname -s)" == Darwin ]]; then
    extension=dylib
fi
if [[ ! -x "$verifier" ]]; then
    echo "Build Verus before rebuilding the TSM library modules." >&2
    exit 1
fi

cd "$repo_dir/source"
"$verifier" \
    --internal-test-mode --is-vstd \
    --extern "verus_builtin=$artifact_dir/libverus_builtin.rlib" \
    --extern "verus_builtin_macros=$artifact_dir/libverus_builtin_macros.$extension" \
    --extern "verus_state_machines_macros=$artifact_dir/libverus_state_machines_macros.$extension" \
    --crate-type=lib \
    --export "$artifact_dir/vstd.vir" --out-dir "$artifact_dir" --compile \
    --cfg 'feature="std"' --cfg 'feature="alloc"' --cfg 'feature="nonzero_internals"' \
    --verify-module resource::tsm --verify-module resource::tsm_storage \
    --verify-module resource::tsm_collections \
    --verify-module resource::tsm_multiset \
    --verify-module resource::tsm_finite_multiset \
    --verify-module resource::tsm_persistent \
    --verify-module resource::tsm_bool \
    --verify-module resource::tsm_helpers \
    --verify-module resource::tsm_context \
    vstd/vstd.rs
