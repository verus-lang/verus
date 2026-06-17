#! /bin/bash -eu

z3_version="4.16.0"

# The OS/libc suffix in each release artifact's name is specific to the Z3
# version (it tracks the platform Z3's CI built that release on), so these
# strings must be revisited on every Z3 upgrade -- they cannot be derived from
# $z3_version alone. See https://github.com/Z3Prover/z3/releases.
if [ `uname` == "Darwin" ]; then
    if [[ $(uname -m) == 'arm64' ]]; then
        filename="z3-$z3_version-arm64-osx-15.7.3"
    elif [[ $(uname -m) == 'x86_64' ]]; then
        filename="z3-$z3_version-x64-osx-15.7.3"
    else
        echo "Unsupported architecture $(uname -m)"
        exit -1
    fi
elif [ `uname` == "Linux" ]; then
    if [[ $(uname -m) == 'aarch64' ]]; then
        filename="z3-$z3_version-arm64-glibc-2.38"
    elif [[ $(uname -m) == 'x86_64' ]]; then
        filename="z3-$z3_version-x64-glibc-2.39"
    else
        echo "Unsupported architecture $(uname -m)"
        exit -1
    fi
elif [[ $(uname) == "MINGW64_NT"* ]]; then
    filename="z3-$z3_version-x64-win"
fi

URL="https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip"

echo "Downloading: $URL"
curl -L -o "$filename.zip" "$URL"
unzip "$filename.zip"

# delete the existing z3 because of caching issue on macs
rm -f z3

cp "$filename/bin/z3" .
echo "z3 located at $(pwd)"
rm -r "$filename"
rm "$filename.zip"
