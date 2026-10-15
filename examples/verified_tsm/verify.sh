#!/usr/bin/env bash
# Run only the proof-producing TSM milestone examples.
set -euo pipefail

example_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd "$example_dir/../.." && pwd)"
verifier="${VERUS_BIN:-$repo_dir/source/target-verus/release/verus}"
log_dir="$(mktemp -d "${TMPDIR:-/tmp}/verified-tsm-examples.XXXXXX")"
passed=0
rejected=0

if [[ ! -x "$verifier" ]]; then
    echo "Build Verus first, or set VERUS_BIN to a built verifier." >&2
    exit 1
fi
verifier_args=(--no-cheating)

for example in "$example_dir"/*.rs; do
    name="$(basename "$example")"
    log="$log_dir/$name.log"
    executable="$log_dir/${name%.rs}"
    echo "Verifying $name"
    if ! "$verifier" "${verifier_args[@]}" --compile -o "$executable" "$example" >"$log" 2>&1; then
        cat "$log"
        echo "Verification failed; logs: $log_dir" >&2
        exit 1
    fi
    if ! grep -Eq 'verification results:: ([0-9]+ verified, 0 errors|verified: [0-9]+ errors: 0)' "$log"; then
        cat "$log"
        echo "No successful verification result; logs: $log_dir" >&2
        exit 1
    fi
    grep 'verification results::' "$log"
    if ! "$executable" >"$log_dir/runtime-$name.log" 2>&1; then
        cat "$log_dir/runtime-$name.log"
        echo "Executable failed; logs: $log_dir" >&2
        exit 1
    fi
    passed=$((passed + 1))
done

for example in "$example_dir"/negative/*.rs; do
    name="$(basename "$example")"
    log="$log_dir/negative-$name.log"
    expected="$(sed -n 's|^// EXPECTED-ERROR: ||p' "$example")"
    if [[ -z "$expected" ]]; then
        echo "Missing EXPECTED-ERROR marker in $example" >&2
        exit 1
    fi
    echo "Checking rejection of $name"
    if "$verifier" "${verifier_args[@]}" "$example" >"$log" 2>&1; then
        cat "$log"
        echo "Expected rejection, but verification succeeded; logs: $log_dir" >&2
        exit 1
    fi
    if ! grep -Fq -- "$expected" "$log"; then
        cat "$log"
        echo "Expected diagnostic was absent; logs: $log_dir" >&2
        exit 1
    fi
    rejected=$((rejected + 1))
done

echo "Verified, compiled, and ran $passed examples; checked $rejected expected rejections."
echo "Logs: $log_dir"
