
set -e
set -x

if [ "$(dirname "$0")" != "." ]; then
    echo "Please run the script from its directory."
    exit 1
fi

docker build -f verus-lang_verus-base.dockerfile -t ghcr.io/utaal/verus-lang/verus-base .
docker build -f verus-lang_verus-base-1.76.0.dockerfile -t ghcr.io/utaal/verus-lang/verus-base:rust-1.76.0 .
docker build -f verus-lang_veritas-1.76.0.dockerfile -t ghcr.io/utaal/verus-lang/veritas:rust-1.76.0 .