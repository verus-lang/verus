#! /bin/bash

set -e

./tools/cargo.sh nextest run "$@"
