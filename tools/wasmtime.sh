#!/usr/bin/env sh

WASMTIME=wasmtime
if ! command -v "$WASMTIME"; then
    WASMTIME="$HOME/.wasm/bin/wasmtime"
fi
exec "$WASMTIME" --dir . "$@"
