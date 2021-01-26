#!/usr/bin/env fish

begin
    set -gx RUST_BACKTRACE 1
    cargo $argv | tools/panic_fmt.rb
end
