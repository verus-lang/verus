#! /bin/bash

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
exec ${DIR}/_common_string_search.sh ./foo.rs "panicked at 'internal error"
