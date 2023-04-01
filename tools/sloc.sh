#!/usr/bin/env bash

set -euo pipefail

function total() {
    cloc --json src lisp \
    | jq '.["Rust"].code + .["C"].code + .["Lisp"].code + .["C/C++ Header"].code'
}

function lisp-tests() {
    cloc --json tests | jq '.["Lisp"].code'
}

function tests() {
    fd . -ers -x awk '/#\[cfg\(test\)\]/{a=1} a; /^}/{a=0}' '{}' \
    | cloc - --force-lang=rust --json \
    | jq '.["SUM"].code'
}

n_total="$(total)"
n_lisp_tests="$(lisp-tests)"
n_rust_tests="$(tests)"
n_tests=$((n_lisp_tests + n_rust_tests))
echo sloc: $((n_total - n_tests))
echo tests sloc: $n_tests
