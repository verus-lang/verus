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

if command -v python3 > /dev/null; then 
    pythoncmd=python3
else
    pythoncmd=python
fi


(
    cd rust
    current_branch=`git branch --show-current`
    if [ "$current_branch" != "verification" ]; then
        echo "ERROR: The verification branch is not checked out in the rust repository."
        echo "To continue, commit you changes and switch back to the verification branch in the rust repository."
        exit 1
    fi

    if [ ! -z "$(git status --porcelain)" ]; then 
        echo "ERROR: The rust checkout in rust/ has a dirty working directory. Updating it may delete your changes."
        echo "To continue, commit you changes and switch back to the verification branch in the rust repository."
        exit 1
    fi

    git fetch origin verification
    git reset --hard origin/verification
    cp config.toml.verify config.toml
    $pythoncmd ./x.py install -i
)

