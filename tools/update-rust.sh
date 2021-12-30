#! /bin/bash

toplevel=`git rev-parse --show-toplevel`

if [ "$toplevel" != "$PWD" ]; then
    echo "ERROR: You should run this script at the root of the verus repository"
    exit 1
fi

if [ ! -d rust ]; then
    echo "The rust/ repository clone is missing. Run tools/set-up-rust.sh first."
    exit 1
fi

(
    cd rust
    current_branch=`git name-rev --name-only HEAD`
    if [ "$current_branch" != "verification" ]; then
        echo "ERROR: The verification branch is not checked out in the rust repository."
        echo "To continue, commit you changes and switch back to the verification branch in the rust repository."
        exit 1
    fi

    if [[ -n $(git status -s) ]]; then
        echo "ERROR: The rust checkout in rust/ has a dirty working directory. Updating it may delete your changes."
        echo "To continue, commit you changes and switch back to the verification branch in the rust repository."
        exit 1
    fi

    git pull --ff-only origin verification
    ./x.py install
)

