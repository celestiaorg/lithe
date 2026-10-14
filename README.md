# Lithe

Lithe is a smart-contract language for the EVM. Entrypoints are state transitions with explicit effects, typed failures, and deterministic storage. The compiler enforces the security rules that Solidity leaves to convention.

> [!WARNING]
> Lithe is in early development and experimental. The language, standard library, and compiler output can change without notice, and neither the compiler nor the standard library has been audited.

```lithe
storage is record {
  count : uint;
}

external view function get() : uint is
  storage.count

external function inc() is {
  storage.count := storage.count + 1;
}
```

- **External calls are deferred.** A state-changing call to another contract runs after the entrypoint has finished its own work, so a callee never sees half-updated state.
- **Typed, declared failures.** Every external function lists the errors it can raise, and the compiler checks the list is complete.
- **Checked effects.** `pure` and `view` are verified against their bodies.
- **Formal verification.** Specs beside the contract are proved with `lithe prove`, against the bytecode the compiler emits.
- **Deterministic storage.** The default layout matches Solidity's; named domains sit at ERC-7201 roots.
- **Modules, not inheritance**, and built-in UUPS upgrades.
- **Smaller bytecode.** About 32% less runtime code than optimized `solc` across real contracts.

## Getting started

Build the compiler with a recent stable Rust toolchain:

```bash
cargo build --release
export PATH="$PWD/target/release:$PATH"
```

Compile a contract and print its ABI:

```bash
lithe compile counter.lithe   # creation bytecode as hex
lithe abi counter.lithe
lithe compile src             # Foundry-style artifacts in ./out
```

Run `lithe` with no arguments for every command. [`lithe prove`](docs/src/pages/language/verification.mdx) also needs [Z3](https://github.com/Z3Prover/z3) on your `PATH`.

## Repository

| Path | Contents |
| --- | --- |
| `src/` | the compiler, CLI, and LSP server |
| `std/` | the standard library, embedded in the compiler at build time |
| `docs/` | the documentation site ([Vocs](https://vocs.dev)); see [docs/README.md](docs/README.md) |
| `playground/` | the compiler built to WebAssembly for the docs site's browser playground |
| `examples/` | example contracts |
| `bench/` | Lithe and Solidity versions of the same contracts, for size and gas comparison (`bench/run.py`) |
| `extensions/` | editor support: a TextMate grammar and a VS Code extension |
| `fuzz/` | extra programs for the differential tests |

Run the tests with `cargo test`.

## Documentation

Start with [Installation and first contract](docs/src/pages/guide/getting-started.mdx), then [The transition model](docs/src/pages/guide/transition-model.mdx) and [Lithe by Example](docs/src/pages/by-example/index.mdx).

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
