#! /bin/bash
z3_version="4.12.5"

filename=z3-$z3_version-x64-glibc-2.31
wget https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip
unzip $filename.zip
cp $filename/bin/z3 .

