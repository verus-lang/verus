
set -e
set -x

if [ "$(dirname "$0")" != "." ]; then
    echo "Please run the script from its directory."
    exit 1
fi

docker push ghcr.io/utaal/verus-lang/verus-deps
docker push ghcr.io/utaal/verus-lang/verus-base:rust-1.82.0
docker push ghcr.io/utaal/verus-lang/veritas:rust-1.82.0
