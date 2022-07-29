#! /bin/bash

set -e

TEMPD=$(mktemp -d)

echo "Running macro expansion on the pervasive lib"

cp -r pervasive $TEMPD
echo "pub mod pervasive;" >> $TEMPD/lib.rs

# verus doesn't exit when we run with unpretty=expanded; work around this by timing out
set +e
timeout 3s ./tools/rust-verify.sh $TEMPD/lib.rs -- -Zunpretty=expanded > $TEMPD/expanded.rs 2> /dev/null
set -e

# sanity check the file got generated
lc=$(cat $TEMPD/expanded.rs | wc -l)
if [ "$lc" -lt "1000" ]; then
    echo "pervasive lib expansion failed"
    exit 1
fi

# The expanded.rs file will have everything inside a `mod pervasive { ... }` block,
# as well as some headers. However, we don't need the headers, and the `mod` block
# would cause the `pervasive` to get doubled-up later since the test files use
# `mod pervasive;`. We strip all this extra stuff out here:
grep '^ ' $TEMPD/expanded.rs > $TEMPD/mod.rs

echo "Expanded pervasive lib at $TEMPD/expanded.rs"

PERVASIVE_PATH=$TEMPD ./tools/cargo.sh test "$@"
