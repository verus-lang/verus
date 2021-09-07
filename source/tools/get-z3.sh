#! /bin/bash

z3_version="4.8.5"

if [ `uname` == "Darwin" ]; then
    wget https://github.com/Z3Prover/z3/releases/download/Z3-$z3_version/z3-$z3_version-x64-osx-10.14.2.zip
    unzip z3-$z3_version-x64-osx-10.14.2.zip
    cp z3-$z3_version-x64-osx-10.14.2/bin/z3 .
    rm -r z3-$z3_version-x64-osx-10.14.2
    rm z3-$z3_version-x64-osx-10.14.2.zip
elif [ `uname` == "Linux" ]; then
    wget https://github.com/Z3Prover/z3/releases/download/Z3-$z3_version/z3-$z3_version-x64-ubuntu-16.04.zip
    unzip z3-$z3_version-x64-ubuntu-16.04.zip
    cp z3-$z3_version-x64-ubuntu-16.04/bin/z3 .
    rm -r z3-$z3_version-x64-ubuntu-16.04
    rm z3-$z3_version-x64-ubuntu-16.04
fi
