#!/usr/bin/env bash
set -e
cd "$(dirname "$0")/.."
source ../tools/activate
vargo build --release --vstd-expand-errors
