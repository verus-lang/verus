#!/usr/bin/env bash

# MC/DC coverage of the verifier crates by the rust_verify_test suite.
#
# Example usage (run from source/):
#
#   ./tools/mcdc.sh                       # vstd build + whole rust_verify_test suite
#   ./tools/mcdc.sh --test modes          # narrow to one suite (args pass to `vargo test`)
#   ./tools/mcdc.sh delta prog.rs [ARGS]  # what one program adds to the last full-suite run
#   ./tools/mcdc.sh clean                 # remove the instrumented worktree and raw records
#
# Options (environment variables):
#
#   JOBS      max concurrent tests / nested build jobs   (default: 4; raise if RAM allows)
#   OUT_DIR   output directory                           (default: mcdc-out/)
#
# The suite runs against an instrumented copy of the repository, never against this checkout:
# a detached git worktree of HEAD in ${OUT_DIR}/build, plus the uncommitted changes to tracked
# files (`git diff HEAD`). Untracked files are not copied. The first run instruments the copy
# and builds it; later runs reuse it, so run `clean` to pick up new source changes.
#
# Outputs in ${OUT_DIR}: manifest.jsonl (one line per decision), records.bin (distinct records
# of this run: vstd build if it ran, then the tests), report/ (summary.md, per-file.tsv,
# decisions.tsv), GAPS.md and GAPS.tsv. A run without test arguments also saves records.bin as
# baseline.bin, which `delta` compares against. See tools/mcdc/README.md.

set -euo pipefail

SOURCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${SOURCE_DIR}" || exit 1

JOBS="${JOBS:-4}"
OUT_DIR="${OUT_DIR:-mcdc-out}"
mkdir -p "${OUT_DIR}"
OUT_DIR="$(cd "${OUT_DIR}" && pwd)"
BUILD="${OUT_DIR}/build"
MANIFEST="${OUT_DIR}/manifest.jsonl"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-${SOURCE_DIR}/z3}"

if [[ "${1:-}" == "clean" ]]; then
	if [[ -d "${BUILD}" ]]; then
		git worktree remove --force "${BUILD}"
	fi
	rm -rf "${OUT_DIR}/records"
	exit 0
fi

# Build the mcdc tool and vargo.
cargo build --release -p mcdc
MCDC="${SOURCE_DIR}/target-verus/release/mcdc"
VARGO_DIR="${SOURCE_DIR}/../tools/vargo"
(cd "${VARGO_DIR}" && cargo build --release)
export PATH="${VARGO_DIR}/target/release:${PATH}"

if [[ "${1:-}" == "delta" ]]; then
	shift
	[[ $# -ge 1 ]] || { echo "usage: $0 delta prog.rs [verus args]" >&2; exit 2; }
	[[ -f "${OUT_DIR}/baseline.bin" ]] || { echo "no ${OUT_DIR}/baseline.bin: run $0 without arguments first" >&2; exit 2; }
	PROG="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
	shift
	REC="$(mktemp -d)"
	trap 'rm -rf "${REC}"' EXIT
	status=0
	MCDC_DIR="${REC}" "${BUILD}/source/target-verus/release/verus" "${PROG}" "$@" >"${REC}/verus.out" 2>&1 || status=$?
	echo "verus exit status ${status}; $(grep -E 'verification results' "${REC}/verus.out" | tail -1)$(grep -m1 -E '^error' "${REC}/verus.out" || true)"
	"${MCDC}" delta "${MANIFEST}" "${OUT_DIR}/baseline.bin" "${REC}"
	exit 0
fi

# Instrumented copy, built once.
if [[ ! -d "${BUILD}" ]]; then
	git worktree add --detach "${BUILD}" HEAD
	git diff --binary HEAD | (cd "${BUILD}" && git apply --allow-empty)
	"${MCDC}" instrument "${BUILD}/source" --in-place --manifest "${MANIFEST}"
fi

# Records of processes started by vargo build (vstd verification, when vstd is rebuilt) and by
# the tests. Each instrumented process appends to its own file in MCDC_DIR.
mkdir -p "${OUT_DIR}/records/vstd"
rm -rf "${OUT_DIR}/records/tests"
mkdir -p "${OUT_DIR}/records/tests"

export CARGO_BUILD_JOBS="${JOBS}"
export RUST_TEST_THREADS="${JOBS}"
SECONDS=0
(cd "${BUILD}/source" && MCDC_DIR="${OUT_DIR}/records/vstd" vargo build --release)
BUILD_SECONDS=${SECONDS}

SECONDS=0
status=0
(cd "${BUILD}/source" && MCDC_DIR="${OUT_DIR}/records/tests" vargo test --release -p rust_verify_test --no-fail-fast "$@") || status=$?
TEST_SECONDS=${SECONDS}

"${MCDC}" compact "${OUT_DIR}/records.bin" "${OUT_DIR}/records/vstd" "${OUT_DIR}/records/tests"
if [[ $# -eq 0 ]]; then
	cp "${OUT_DIR}/records.bin" "${OUT_DIR}/baseline.bin"
fi
"${MCDC}" report "${MANIFEST}" "${OUT_DIR}/records.bin" --out "${OUT_DIR}/report"
"${MCDC}" gaps "${MANIFEST}" "${OUT_DIR}/records.bin" --out "${OUT_DIR}"

echo "build: ${BUILD_SECONDS} s; tests: ${TEST_SECONDS} s; test exit status: ${status}"
echo "summary: ${OUT_DIR}/report/summary.md"
echo "gaps:    ${OUT_DIR}/GAPS.md"
exit "${status}"
