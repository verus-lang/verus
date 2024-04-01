#! /bin/bash

set -e

for file in `ls .verus-log/*.dot`; do
    from=$file
    to="${file%.*}.pdf"
    set -x
    dot -Tpdf $from > $to
    set +x
    echo -e "$from -> \033[1;94m$to\033[0m"
done
