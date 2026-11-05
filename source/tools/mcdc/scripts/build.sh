#!/usr/bin/env bash

# Builds an instrumented Verus in a detached worktree of HEAD (plus the uncommitted changes to
# tracked files), as tools/mcdc.sh does.
#
# Usage (from source/):
#
#   tools/mcdc/scripts/build.sh mcdc OUT      # build A: MC/DC only (`mcdc instrument`)
#   tools/mcdc/scripts/build.sh mutants OUT   # build B: MC/DC + mutant schemata (`mcdc mutate`)
#
# Environment:
#
#   JOBS         nested build jobs (default 4)
#   FILES        list of the files to mutate (default: every file of the instrumented crates;
#                tools/mcdc/mutate-files.txt lists the 23 priority files)
#   DISABLE      disable list (default tools/mcdc/mutate-disable.txt); build B appends to it the
#                points that do not compile, then regenerates and rebuilds, at most ROUNDS times
#   ROUNDS       default 20
#   MUTANTS_OFF  1: build B with every mutant compiled off (the runtime refuses MUTANT_BITSET)
#   WRAP         command prefix for each vargo build (for example a timeout or a job limiter)
#
# Outputs in OUT: build/ (the worktree; the verus binary is build/source/target-verus/release/verus),
# map/ (manifest.jsonl, and for build B mutants.tsv and decisions.tsv), logs/build-<n>.log.

set -euo pipefail

MODE="${1:?usage: build.sh mcdc|mutants OUT}"
OUT="${2:?usage: build.sh mcdc|mutants OUT}"
SOURCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
TOOL="${SOURCE_DIR}/tools/mcdc"
cd "${SOURCE_DIR}"
JOBS="${JOBS:-4}"
FILES_ARG=()
if [[ -n "${FILES:-}" ]]; then
	FILES_ARG=(--files "$(cd "$(dirname "${FILES}")" && pwd)/$(basename "${FILES}")")
fi
DISABLE="${DISABLE:-${TOOL}/mutate-disable.txt}"
ROUNDS="${ROUNDS:-20}"
WRAP="${WRAP:-}"
CRATES="vir rust_verify air builtin_macros state_machines_macros"

mkdir -p "${OUT}"
OUT="$(cd "${OUT}" && pwd)"
BUILD="${OUT}/build"
MAP="${OUT}/map"
mkdir -p "${MAP}" "${OUT}/logs"
touch "${DISABLE}"
DISABLE="$(cd "$(dirname "${DISABLE}")" && pwd)/$(basename "${DISABLE}")"

cargo build --release -p mcdc
MCDC="${SOURCE_DIR}/target-verus/release/mcdc"
VARGO_DIR="${SOURCE_DIR}/../tools/vargo"
(cd "${VARGO_DIR}" && cargo build --release)
export PATH="${VARGO_DIR}/target/release:${PATH}"
export VERUS_Z3_PATH="${VERUS_Z3_PATH:-${SOURCE_DIR}/z3}"

if [[ ! -d "${BUILD}" ]]; then
	git worktree add --detach "${BUILD}" HEAD
	git diff --binary HEAD > "${OUT}/local.patch"
	(cd "${BUILD}" && git apply --allow-empty "${OUT}/local.patch")
	[[ -f "${SOURCE_DIR}/z3" ]] && cp "${SOURCE_DIR}/z3" "${BUILD}/source/z3"
fi
S="${BUILD}/source"

restore() {
	# undo a previous rewrite of the crates (instrumentation and runtime files)
	for c in ${CRATES}; do
		git -C "${BUILD}" checkout -q HEAD -- "source/${c}"
		git -C "${BUILD}" clean -fdq -- "source/${c}/src"
	done
	local inc=()
	for c in ${CRATES}; do inc+=(--include="source/${c}/*"); done
	(cd "${BUILD}" && git apply --allow-empty "${inc[@]}" "${OUT}/local.patch")
}

rewrite() {
	restore
	if [[ "${MODE}" == mcdc ]]; then
		"${MCDC}" instrument "${S}" --in-place --manifest "${MAP}/manifest.jsonl"
	else
		local off=()
		[[ "${MUTANTS_OFF:-0}" == 1 ]] && off=(--mutants-off)
		"${MCDC}" mutate "${S}" ${FILES_ARG[@]+"${FILES_ARG[@]}"} --disable "${DISABLE}" --map-dir "${MAP}" ${off[@]+"${off[@]}"}
	fi
}

build() {
	local log="$1" st=0
	(cd "${S}" && CARGO_BUILD_JOBS="${JOBS}" ${WRAP} vargo build --release) > "${log}" 2>&1 || st=$?
	echo "EXIT ${st}" >> "${log}"
	return "${st}"
}

case "${MODE}" in
mcdc)
	rewrite | tail -12
	build "${OUT}/logs/build-1.log" && { grep -E "verification results" "${OUT}/logs/build-1.log" | tail -1; echo "build A: ${S}/target-verus/release/verus"; exit 0; }
	echo "build failed: ${OUT}/logs/build-1.log" >&2
	exit 1
	;;
mutants)
	for i in $(seq 1 "${ROUNDS}"); do
		rewrite | grep -E "^mutants:|^commit"
		log="${OUT}/logs/build-${i}.log"
		if build "${log}"; then
			grep -E "verification results" "${log}" | tail -1
			echo "round ${i}: build B OK: ${S}/target-verus/release/verus"
			exit 0
		fi
		res="$(python3 "${TOOL}/scripts/fixbuild.py" "${log}" "${MAP}" "${S}" "${DISABLE}")"
		echo "round ${i}: ${res}" | head -20
		if echo "${res}" | grep -q 'new disable entries: 0'; then
			echo "no progress; see ${log}" >&2
			exit 1
		fi
	done
	echo "still failing after ${ROUNDS} rounds" >&2
	exit 1
	;;
*)
	echo "unknown mode ${MODE}" >&2
	exit 2
	;;
esac
