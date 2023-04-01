export MIRIFLAGS := "-Zmiri-disable-isolation -Zmiri-tag-raw-pointers"

install-tools:
    command -v cargo-hack &>/dev/null || cargo install cargo-hack
    rustup component add miri
    rustup target add wasm32-unknown-unknown
    rustup target add x86_64-unknown-linux-musl
    rustup target add x86_64-unknown-linux-gnu

test-all: install-tools
    cargo hack test --feature-powerset
    cargo build --features "wasm" --target wasm32-unknown-unknown
    cargo build --target x86_64-unknown-linux-musl
    cargo build --target x86_64-unknown-linux-gnu
    cargo miri test

default:
    @just --list
