#!/bin/sh
# Builds the compiler to WebAssembly for the docs site's playground, at /playground.
set -e
cd "$(dirname "$0")"
cargo build --release --locked
cp target/wasm32-unknown-unknown/release/lithe_playground.wasm ../docs/public/play/lithe.wasm

