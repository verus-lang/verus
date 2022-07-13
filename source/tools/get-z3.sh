#! /bin/bash

z3_version="4.9.1"

if [ `uname` == "Darwin" ]; then
    filename=z3-$z3_version-x64-osx-10.16
    wget https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip
    unzip $filename.zip
    cp $filename/bin/z3 .
    rm -r $filename
    rm $filename.zip
elif [ `uname` == "Linux" ]; then
    filename=z3-$z3_version-x64-glibc-2.31
    wget https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip
    unzip $filename.zip
    cp $filename/bin/z3 .
    rm -r $filename
    rm $filename.zip
fi
