# AGENTS.md

Lithe is a smart-contract language for the EVM. This repository holds the compiler (Rust), its standard library (Lithe), the docs site, and editor and Hardhat tooling. See [README.md](README.md) for the language overview and the directory map.

## Build and test

```bash
cargo build --release          # target/release/lithe
cargo test --locked            # the full suite: parser, checker, codegen run on revm, prover
cargo test --locked <name>     # one test or module
```

- The dev profile is `opt-level = 2` on purpose; the optimizer is too slow unoptimized.
- `std/` is embedded at build time by `build.rs`. Edits to `std/` need a rebuild before the binary or tests see them.
- `lithe prove` builds Z3 from source (needs CMake, Python 3, a C++ compiler). The first build is slow.

## Checks CI runs

Run what applies to your change before you say it's done:

```bash
cargo fmt --check && cargo clippy --all-targets -- -D warnings
(cd playground && cargo fmt --check && cargo clippy --all-targets -- -D warnings)
cargo machete
(cd docs && npm ci && npm run lint)                   # prettier + tsc
sh extensions/sync-grammar.sh && git diff --exit-code  # after editing extensions/lithe.tmLanguage.json
git ls-files -z '*.sh' | xargs -0 shellcheck
target/release/lithe prove <file>.lithe               # for every file with a .spec.lithe beside it
(cd docs && npm run check)                            # every ```lithe block in the docs compiles
```

`.github/workflows/ci.yml` is the source of truth.

## Where things go

- `src/`: compiler, CLI (`src/main.rs`), LSP. Codegen is in `src/gen` and `src/asm`, the prover in `src/prove`, and the runtime tests in `src/evm`.
- `src/evm/matrix.rs` crosses every type with every place a value can live. Extend it when you add a type, a place, or a feature that touches either.
- `examples/reject/`: programs that must fail to compile. Each needs a rule in `src/evm/examples.rs`.
- `bench/`: each contract in Lithe and Solidity. `python3 bench/run.py [name ...]` compares size and gas on anvil (needs Foundry and solc).
- `docs/src/pages`: MDX docs. Mark a ```lithe block `fragment`, `rejects`, or `[file.lithe]` as described in `docs/README.md`.

## Conventions

- Lithe code: camelCase values, PascalCase types, errors, and events. Format with `lithe fmt`.
- Lithe has no users yet. Replace old syntax outright; don't add migration errors or deprecated aliases.
- Compiler output changes are judged on gas first and bytecode size second. Measure with `bench/run.py` against the pre-change build. The differential tests (`src/evm/differential.rs`, over `examples/` and `fuzz/`) replay random calls against two builds of each program to catch miscompiles; add a `fuzz/` program when an optimization needs coverage the examples lack.
- Docs examples stand alone; don't reference external projects being ported.
- Comments explain non-obvious intent. No changelog-style comments.

## Commits

- Write plain commit messages. Do not add `Co-Authored-By` trailers or any other AI attribution to commits or PR bodies.
- Don't commit or push unless asked.
