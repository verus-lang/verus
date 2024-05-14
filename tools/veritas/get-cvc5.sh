#! /bin/bash

cvc5_version=$1
destination=$2

if [ `uname` == "Darwin" ]; then
    if [[ $(uname -m) == 'arm64' ]]; then
        filename=cvc5-macOS-arm64-static
    else
        filename=cvc5-macOS-static
    fi
elif [ `uname` == "Linux" ]; then
    filename=cvc5-Linux-static
fi

wget https://github.com/cvc5/cvc5/releases/download/cvc5-$cvc5_version/$filename.zip
unzip $filename.zip

# delete the existing cvc5 because of caching issue on macs
rm -f cvc5

cp $filename/bin/cvc5 $destination
rm -r $filename
rm $filename.zip
