#! /bin/bash -eu

z3_version="4.12.5"

if [ `uname` == "Darwin" ]; then
    if [[ $(uname -m) == 'arm64' ]]; then
        filename="z3-$z3_version-arm64-osx-11.0"
    elif [[ $(uname -m) == 'x86_64' ]]; then
        filename="z3-$z3_version-x64-osx-11.7.10"
    else
        echo "Unsupported architecture $(uname -m)"
        exit -1
    fi
elif [ `uname` == "Linux" ]; then
    if [[ $(uname -m) == 'aarch64' ]]; then
        filename="z3-$z3_version-arm64-glibc-2.35"
    elif [[ $(uname -m) == 'x86_64' ]]; then
        filename="z3-$z3_version-x64-glibc-2.31"
    else
        echo "Unsupported architecture $(uname -m)"
        exit -1
    fi
fi

URL="https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip"

echo "Downloading: $URL"
curl -L -o "$filename.zip" "$URL"
unzip "$filename.zip"

# delete the existing z3 because of caching issue on macs
rm -f z3

cp "$filename/bin/z3" .
rm -r "$filename"
rm "$filename.zip"
