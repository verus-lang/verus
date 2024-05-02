set -e
set -x

z3_version=$1
destination=$2

if [ ! `uname` == "Linux" ]; then
    echo "unexpected OS"
    exit 1
fi

filename=z3-$z3_version-x64-glibc-2.31

wget https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip
unzip $filename.zip

cp $filename/bin/z3 $destination
rm -r $filename
rm $filename.zip