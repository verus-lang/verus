#! /bin/bash

set -eu

z3_version="4.10.1"

UNAME=$(uname)

if [ "$UNAME" = "Darwin" ]; then
  if [ "$(uname -m)" = "arm64" ]; then
    filename=z3-$z3_version-arm64-osx-11.0
  else
    filename=z3-$z3_version-x64-osx-10.16
  fi
elif [ "$UNAME" = "Linux" ]; then
  filename=z3-$z3_version-x64-glibc-2.31
fi

if [ -x z3 ]; then
  if ./z3 --version | grep "$z3_version" >/dev/null 2>&1; then
    echo "z3 $z3_version found"
    exit 0
  fi
fi

wget "https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip"
unzip -o "$filename".zip "$filename"/bin/z3
rm "$filename".zip
