set positional-arguments

export MIRIFLAGS := "-Zmiri-disable-isolation"
export CARGO_TARGET_WASM32_WASI_RUNNER := "tools/wasmtime.sh"
export WASMTIME_BACKTRACE_DETAILS := "1"

install-tools:
    command -v cargo-hack &>/dev/null || cargo install cargo-hack
    rustup component add miri
    rustup target add wasm32-unknown-unknown
    rustup target add x86_64-unknown-linux-musl
    rustup target add x86_64-unknown-linux-gnu

test:
    cargo test

test-wasm:
    cargo test --target wasm32-wasi

build-wasm:
    cargo build --profile wasm \
                --target wasm32-unknown-unknown \
                -Z build-std=std,panic_abort \
                -Z build-std-features=panic_immediate_abort \
                --no-default-features \
                --features wasm
    mkdir -p target/wasm-opt
    @echo "optimizing wasm files ..."
    fd . -d1 -ewasm target/wasm32-unknown-unknown/wasm \
         -x wasm-opt -Oz -o target/wasm-opt/{/} {}
    @echo "optimized wasm files saved to target/wasm-opt"

test-all: install-tools
    just build-wasm
    just test-wasm
    cargo hack test --feature-powerset
    cargo build --target x86_64-unknown-linux-musl
    cargo build --target x86_64-unknown-linux-gnu
    cargo miri test

@miri *args:
    cargo miri "$@"

default:
    @just --list
