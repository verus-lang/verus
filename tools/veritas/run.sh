#! /bin/bash

RUST_VERSION=1.88.0

if [ "$(dirname "$0")" != "." ]; then
    echo "Please run the script from its directory."
    exit 1
fi

if command -v docker >/dev/null 2>&1; then
    RUNTIME=docker
elif command -v podman >/dev/null 2>&1; then
    RUNTIME=podman
else
    echo "Neither docker nor podman found."
    exit 1
fi

HOST_WORK_DIR="${HOST_WORK_DIR:-/tmp/veritas-work}"
mkdir -p "$HOST_WORK_DIR" output

# Optional: mount a local Verus checkout for file:// verus_git_url in config.
# Example:
#   LOCAL_VERUS_REPO=/home/user/work/verus \
#   bash run.sh run_configuration_local.toml
EXTRA_MOUNTS=()
if [ -n "${LOCAL_VERUS_REPO:-}" ]; then
    if [ ! -d "$LOCAL_VERUS_REPO" ]; then
        echo "LOCAL_VERUS_REPO is not a directory: $LOCAL_VERUS_REPO"
        exit 1
    fi
    EXTRA_MOUNTS+=("-v" "$LOCAL_VERUS_REPO:/root/local-verus")
fi

"$RUNTIME" run --platform=linux/amd64 \
    -v verus-veritas-repo-cache:/root/repos-cache \
    -v $(pwd):/root/veritas \
    -v "$HOST_WORK_DIR":/root/work \
    -v verus-veritas-cargo-$RUST_VERSION-cache:/root/.cargo \
    -v verus-veritas-z3-cache:/root/z3-cache \
    -v verus-veritas-rustup-$RUST_VERSION:/root/.rustup \
    -v $(pwd)/output:/root/output \
    "${EXTRA_MOUNTS[@]}" \
    --rm \
    veritas:rust-$RUST_VERSION $@
