#!/usr/bin/env fish

set -l bin $argv[1]
set -l tries 80

#set -gx RUSTFLAGS "-C target-cpu=native"

cargo build --release --bin $bin
or exit 1

set compute (dirname (status -f))/avg_compute.awk
set arg_fmt (string join "_" $argv | string replace -a "/" "%%")
set csvout stats/run_times_$arg_fmt.csv

for i in (seq $tries)
    begin
        set -lx LC_NUMERIC en_US.UTF-8
        perf stat -x',' target/release/$bin $argv[2..-1] 1>/dev/null
        or exit 1
    end &| awk -vFS=',' '$2 == "msec" { print $1 }'
    echo -n "·" 1>&2
end | awk -v CSVOUT=$csvout -f $compute | read avg min max med std

echo 1>&2
echo Average: $avg msec
echo Median: $med msec
echo Stddev: $std
echo Minimum: $min msec
echo Maximum: $max msec
