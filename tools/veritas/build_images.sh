
set -e
set -x

RUST_VERSION=1.88.0

if [ "$(dirname "$0")" != "." ]; then
    echo "Please run the script from its directory."
    exit 1
fi

docker build -f verus-lang_verus-deps.dockerfile -t verus-deps .
docker build -f verus-lang_verus-base-$RUST_VERSION.dockerfile -t verus-base:rust-$RUST_VERSION .
docker build -f verus-lang_veritas-$RUST_VERSION.dockerfile -t veritas:rust-$RUST_VERSION .
