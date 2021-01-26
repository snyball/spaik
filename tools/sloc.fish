#!/usr/bin/env fish

## Count up all the lines of code, but show cargo tests seperately.

set total (cloc --json src lisp \
          | jq '.["Rust"].code + .["C"].code + .["Lisp"].code + .["C/C++ Header"].code')
set lisp_tests (cloc --json tests \
               | jq '.["Lisp"].code')
set tests (fd . -ers -x awk '/#\[cfg\(test\)\]/{a=1} a; /^}/{a=0}' '{}' \
          | cloc - --force-lang=rust --json \
          | jq '.["SUM"].code')
echo Project: (math $total - $tests) sloc
echo Tests: (math $tests + $lisp_tests) sloc
