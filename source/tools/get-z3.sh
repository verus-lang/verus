#! /bin/bash

z3_version="4.12.2"

if [ `uname` == "Darwin" ]; then
    if [[ $(uname -m) == 'arm64' ]]; then
        filename=z3-$z3_version-arm64-osx-11.0
    else
        filename=z3-$z3_version-x64-osx-10.16
    fi
elif [ `uname` == "Linux" ]; then
    filename=z3-$z3_version-x64-glibc-2.31
fi

wget https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip
unzip $filename.zip
cp $filename/bin/z3 .
rm -r $filename
rm $filename.zip
