set positional-arguments

export MIRIFLAGS := "-Zmiri-disable-isolation -Zmiri-tree-borrows"
export CARGO_TARGET_WASM32_WASIP1_RUNNER := "tools/wasmtime.sh"
export WASMTIME_BACKTRACE_DETAILS := "1"

install-tools:
    command -v cargo-hack &>/dev/null || cargo install cargo-hack
    rustup +nightly component add miri
    rustup target add wasm32-unknown-unknown
    rustup target add wasm32-wasip1
    rustup target add x86_64-unknown-linux-musl
    rustup target add x86_64-unknown-linux-gnu

test:
    cargo test

test-wasm:
    cargo test --target wasm32-wasip1 -- --nocapture

build-wasm:
    cargo +nightly build --profile wasm \
                --target wasm32-unknown-unknown \
                --features serde \
                -Z build-std=std,panic_abort \
                -Z build-std-features=panic_immediate_abort \
                --no-default-features \
                --features wasm
    mkdir -p target/wasm-opt
    @echo "optimizing wasm files ..."
    fd . -d1 -ewasm target/wasm32-unknown-unknown/wasm \
         -x wasm-opt -Oz -o target/wasm-opt/{/} {}
    @echo "optimized wasm files saved to target/wasm-opt"

build-mini:
    cargo build --profile wasm \
                --target x86_64-unknown-linux-gnu \
                -Z build-std=std,panic_abort \
                -Z build-std-features=panic_immediate_abort \
                --no-default-features

before-commit:
    cargo check
    cargo test
    @just test-wasm

test-all: install-tools
    cargo test
    @just test-wasm
    @echo "testing with miri, this will take a long time"
    @just test-miri
    @just test-miri-32
    #cargo hack test --feature-powerset

@miri *args:
    cargo miri "$@"

test-miri:
    cargo +nightly miri test

test-miri-32:
    cargo +nightly miri --target i686-unknown-linux-gnu test

default:
    @just --list
