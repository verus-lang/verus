#! /bin/bash

toplevel=`git rev-parse --show-toplevel`

if [ "$toplevel" != "$PWD" ]; then
    echo "ERROR: You should run this script at the root of the verus repository"
    exit 1
fi

if [ -d rust ]; then
    echo "ERROR: The rust/ directory already exists. Have you run this script already?"
    echo "To continue, remove the rust/ directory and re-run the script."
    exit 1
fi

git clone git@github.com:secure-foundations/rust.git
