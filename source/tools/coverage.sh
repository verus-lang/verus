#!/usr/bin/env bash

# Code coverage for the rust_verify_test suite.
#
# Example usage (run from source/):
#
#   ./tools/coverage.sh                    # whole rust_verify_test suite (slow)
#   ./tools/coverage.sh --test bitvector   # narrow to one suite (args pass to `vargo test`)
#
# Options (environment variables):
#
#   JOBS      max concurrent tests / nested build jobs   (default: 4; raise if RAM allows)
#   OUT_DIR   output directory for coverage reports      (default: coverage/)

# Note: coverage collection is non-standard because the rust_verify_test suite
# is non-standard: the code under test is not the test binary itself, but the
# `rust_verify` binary that the tests spawn.  So we have to configure coverage
# collection for the spawned processes, not the test binary.

set -euo pipefail

# Resolve source/ and run from there.
SOURCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${SOURCE_DIR}" || exit 1

# Cap concurrency. A full test suite run is memory-intensive and spawns many
# subprocesses.  Low default, increase if resources allow.
JOBS="${JOBS:-4}"
OUT_DIR="${OUT_DIR:-coverage}"

# Build vargo and put it on PATH.
VARGO_DIR="${SOURCE_DIR}/../tools/vargo"
(cd "${VARGO_DIR}" && cargo build --release)
export PATH="${VARGO_DIR}/target/release:${PATH}"

# Locate LLVM tools from the pinned toolchain's llvm-tools component.
SYSROOT="$(rustc --print sysroot)"
HOST="$(rustc -vV | sed -n 's/host: //p')"
LLVM_BIN="${SYSROOT}/lib/rustlib/${HOST}/bin"
export PATH="${LLVM_BIN}:${PATH}"

# Binary under test to pass to llvm-cov reporting.
BIN="target-verus/release/rust_verify"

# Directory for profiling data output, cleaned on exit.
PROF_DIR="$(mktemp -d)"
trap 'rm -rf "${PROF_DIR}"' EXIT

# Configure Z3 path, defaulting to downloaded copy in source/ directory.
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-${SOURCE_DIR}/z3}"

# Rust flags to instrument for coverage.
export RUSTFLAGS="-C instrument-coverage ${RUSTFLAGS:-}"

# Build the instrumented binary.
#
# Skip vstd's SMT verification. Building still runs instrumented code, so route
# to its own set of profiling data files.
export LLVM_PROFILE_FILE="${PROF_DIR}/build-%m.profraw"
vargo build --release --vstd-no-verify

# Run the suite under bounded concurrency.
#
# RUST_TEST_THREADS caps how many tests run at once; CARGO_BUILD_JOBS caps the
# nested project builds inside the `cargo` tests.  Each spawned rust_verify
# writes under the test prefix, pooled into $JOBS files.
export RUST_TEST_THREADS="${JOBS}"
export CARGO_BUILD_JOBS="${JOBS}"
export LLVM_PROFILE_FILE="${PROF_DIR}/test-%${JOBS}m.profraw"
vargo test --release -p rust_verify_test "$@"

# Merge the test profraw.
#
# Only the test-* prefix; the build-* prefix is left for the trap to clean.
llvm-profdata merge -sparse "${PROF_DIR}"/test-*.profraw -o "${PROF_DIR}/cov.profdata"

# Generate the coverage report.
#
# Scoped to SOURCE_DIR; llvm-cov only reports files that have coverage maps in
# the binary, so this keeps the verus crates and drops external deps
# automatically.
mkdir -p "${OUT_DIR}"
llvm-cov show -format=html -output-dir="${OUT_DIR}" \
	--instr-profile="${PROF_DIR}/cov.profdata" "${BIN}" "${SOURCE_DIR}"
llvm-cov export -format=lcov \
	--instr-profile="${PROF_DIR}/cov.profdata" "${BIN}" "${SOURCE_DIR}" >"${OUT_DIR}/coverage.lcov"

echo "report: ${OUT_DIR}/index.html"
echo "lcov:   ${OUT_DIR}/coverage.lcov"
