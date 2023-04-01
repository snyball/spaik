#!/usr/bin/env bash

set -euo pipefail

declare bin="$1"
declare -i tries=80

cargo build --release --bin "$bin"

compute="$(dirname "$0")/avg_compute.awk"

function run() {
    local -x LC_NUMERIC=en_US.UTF-8
    perf stat -x',' -- "target/release/${bin}" "$@" >/dev/null
}

{
    for _ in $(seq $tries); do
        run "$@" 2>&1 | awk -vFS=',' '$2 == "msec" {print $1}'
        echo -n "·" 1>&2
    done
    echo 1>&2
} | awk -v CSVOUT='' -f "$compute"
