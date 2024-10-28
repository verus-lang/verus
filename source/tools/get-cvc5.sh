#! /bin/bash -eu

cvc5_version="1.1.2"

if [ `uname` == "Darwin" ]; then
    if [[ $(uname -m) == 'arm64' ]]; then
        filename="cvc5-macOS-arm64-static"
    else
        filename="cvc5-macOS-static"
    fi
elif [ `uname` == "Linux" ]; then
    filename="cvc5-Linux-static"
fi

URL="https://github.com/cvc5/cvc5/releases/download/cvc5-$cvc5_version/$filename.zip"

echo "Downloading: $URL"
curl -L -o "$filename.zip" "$URL"
unzip "$filename.zip"

# delete the existing cvc5 because of caching issue on macs
rm -f cvc5

cp "$filename/bin/cvc5" .
rm -r "$filename"
rm "$filename.zip"
