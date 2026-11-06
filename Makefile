# `make check` runs what every commit must pass.
.PHONY: check fmt clippy test verify differential snapshot bench-gas wasm

check: fmt clippy test verify differential snapshot bench-gas wasm

fmt:
	cargo fmt --check
	cd playground && cargo fmt --check

clippy:
	cargo clippy --all-targets -- -D warnings
	cd playground && cargo clippy --all-targets -- -D warnings

test:
	cargo test --locked

# The whole suite with promotion and range queries checked against fresh analyses.
verify:
	LITHE_VERIFY=1 cargo test --locked

differential:
	LITHE_FUZZ_STEPS=2000 cargo test --locked --lib evm::differential

snapshot:
	cargo test --locked --lib evm::snapshot

bench-gas:
	LITHE_BENCH_GAS=1 cargo test --locked --lib evm::bench_gas -- --include-ignored

wasm:
	cd playground && cargo build --release --locked
