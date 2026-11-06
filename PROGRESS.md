# Lithe compiler speed

Measured speed work on this branch. Security and bytecode invariants in the program prompt still hold. Every number quoted from a task comes from `scripts/bench_compile.py` (`LITHE_CACHE_DIR` empty, `LITHE_TIME=1`). The full record is `baseline.json`. The prompt's v0.3.0 timings are stale; this tree is v0.4.0 and was re-measured here.

## Decisions

1. **Default optimization level.** `Options::default()` stays `opt: Release`, so the public API, playground, cache key, and existing tests keep their meaning. The CLI and `lithe::analyze` will default to Fast. `--release` or `lithe.toml` `[build] opt = "release"` selects Release. Standard JSON takes `settings.lithe.opt` through `set_build_option("opt", ..)`. `bench/run.py` passes `--release`. Fast gets its own snapshot, differential, and size-limit tests.
2. **Byte-identical gate.** SHA-256 of creation and runtime bytecode per contract per mode, in `tests/snapshots/bytecode.json`. Non-codegen steps leave it unchanged. Codegen steps regenerate it with a written justification and the gas and size delta.
3. **Gas without solc.** `src/evm/bench_gas.rs` writes `{suite: {runtime_bytes, deploy_gas, gas, outcomes}}` to `$LITHE_BENCH_OUT`. `scripts/bench_compile.py` invokes that test and stores it under `gas`. Runtime bytes for every harness target come from that target's compile artifacts. The 1% gas gate compares totals only when every suite's outcomes vector is unchanged. An outcome change is a behaviour change and fails the gate.
4. **Timers.** Atomics, read only when `LITHE_TIME` is set. Sums are CPU-seconds. Headline numbers use `LITHE_THREADS=1`. One contract per process, because the counters are process-global.
5. **Dependencies.** No new crates in Phases 0–2. Phase 3+ may propose `rustc-hash` or `indexmap` only with a measured win. Nothing new in the wasm build.

## Tasks

### Phase 0 — harness and safety net

- [x] **0.1** Timers and counters behind `LITHE_TIME`, `LITHE_THREADS`, `[profile.fast]`.
- [x] **0.2a** `scripts/gen_scaling.py`, `src/evm/bench_gas.rs`, and the opt-in gas meter.
- [x] **0.2a′** All `bench/run.py` suites, multi-deploy, in-harness signing.
- [x] **0.2a″** Stale storage on reentry fixed in the interpreter; per-step outcomes recorded. Landed before `baseline.json`.
- [x] **0.2b** `scripts/bench_compile.py`, `baseline.json`, this file. Release only (Fast is 1.1). See the measurements below.
- [x] **0.3** Release bytecode snapshot over `bench/`, `examples/`, and `fuzz/`.
- [x] **0.4** `compare_modes`, `fast_matches_release` (Release vs Release until 1.1), `bench/` in `differential_targets`, `LITHE_VERIFY`, and `make check`.

### Phase 1 — stop compiling the contract 50–100 times

- [ ] **1.1** `Opt { Fast, Release }` (`Default` = Release). Fast is one build of the `start` plan, plus the size-limit outline-more loop. CLI, `lithe.toml`, Standard JSON, and `analyze` wired as in decision 1.
- [ ] **1.2** Differential Fast vs Release over every target; Fast snapshot. Record erc20_full Fast time and the Fast-vs-Release size and gas table. Target ≤ 60 ms.
- [ ] **1.3** Cheaper Release search, byte-identical: dedupe plans, post-promote finish cache, lower-bound short-circuit, share `flow`/`heat` in `asm::gas`.
- [ ] **1.4** Per-function body memo in `Gen`. Release byte-identical.

### Phase 2 — the language server never runs codegen on a keystroke

- [ ] **2.1** `analyze_frontend` / `analyze_full`. LSP uses the frontend on open and change. Codegen errors on save, on a worker, cancelled when a newer edit arrives.
- [ ] **2.2** Per-session module cache keyed by path, content hash, and EVM version. `std/` parsed once per process.
- [ ] **2.3** Debounce `didChange` (~50 ms), reader thread plus worker, rename, workspace symbol. Diagnostics on `bench/erc20_full.lithe` ≤ 20 ms (relaxed under `debug_assertions`).
- [ ] **2.4** VS Code extension and TextMate smoke test.

### Phase 3 — block IR, one-shot stack scheduling, linear passes

- [ ] **3.1** CFG over `Vec<Inst>` and per-block worklist rewrites. Byte-identical in both modes.
- [ ] **3.2** `peephole` and `schedule` per block. Delete the 500-round loop. Byte-identical.
- [ ] **3.3** Per-function stack scheduler. Spill to the memory home past DUP16/SWAP16. Differential at `LITHE_FUZZ_STEPS=5000`, prove tests, snapshot regenerated, gas outcomes unchanged and totals within 1%.
- [ ] **3.4** `outline` on the block IR.
- [ ] **3.5** Ladder: per-line `promote`+`optimize` cost from 439 to 1735 lines ≤ 1.5×.

### Phase 4 — parallelism inside one build

- [ ] **4.1** Per-function parallel emit, schedule, and optimize. Deterministic join. Wasm stays single-threaded. Test `LITHE_THREADS=1` vs N.
- [ ] **4.2** Overlap sibling `check` and `route::abi` with codegen. Determinism test.

### Phase 5 — frontend hygiene and caching

- [ ] **5.1** Identifier interner.
- [ ] **5.2** `FileId` and byte `Span`. Diagnostics keep `line` and `column`.
- [ ] **5.3** Remove deep clones. Make `Plan` cheap.
- [ ] **5.4** Fx hasher. `IndexMap` where order is observable.
- [ ] **5.5** Index-arena AST.
- [ ] **5.6** Parsed and checked module cache across `compile_dir` and `abi_dir`.
- [ ] **5.7** Lexer slices and statement-level parser recovery. First error unchanged.

### Phase 6 — evaluate and take if they pay

- [ ] **6.1** Process startup.
- [ ] **6.2** Assembler width fixpoint, if it is not already one.
- [ ] **6.3** Memoize constant keccak.
- [ ] **6.4** Incremental `heat` / `flow`.
- [ ] **6.5** `--timings`, and CI that fails when erc20_full Fast compile exceeds 2× the recorded baseline.

## 0.2b baseline

Commit `796fdfe6ba4002c9731971cf2248ebf62162c0e9`, `target/release/lithe`, 16 cores. `python3 scripts/bench_compile.py -o baseline.json`. Cache forced off. 127 targets: 51 `bench/*.lithe`, 71 `examples/` files that pass `differential_targets`, and the ladder at N = 16/32/64/128/256. Release is the only mode. `1` is `LITHE_THREADS=1`; `16` is every core. Compile wall time includes process startup. Phase times are the `[time]` line, and the sums are CPU-seconds. Runtime bytes sum the contract and its facet artifacts. `/usr/bin/time` reports CPU only to a centisecond, so a compile under 10 ms shows `cpu_s` of 0.

| target | lines | abi ms | abi lines/s | compile ms (1) | lines/s (1) | compile ms (16) | check ms | backend ms | emits | finishes | promote ms | optimize ms | outline ms | creation | runtime |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `bench/counter.lithe` | 48 | 6.1 | 7833 | 7.3 | 6584 | 6.5 | 0.1 | 1.6 | 16 | 4 | 0.4 | 0.2 | 0.3 | 235 | 198 |
| `bench/solady_erc20.lithe` | 176 | 6.7 | 26316 | 40.2 | 4383 | 27.8 | 0.3 | 32.2 | 28 | 22 | 7.1 | 7.5 | 8.5 | 1405 | 1395 |
| `bench/uniswap_v2_pair.lithe` | 529 | 6.6 | 80261 | 338.6 | 1562 | 139.4 | 0.5 | 330.7 | 37 | 33 | 109.1 | 56.6 | 95.3 | 5267 | 5073 |
| `bench/erc1155.lithe` | 158 | 7.8 | 20314 | 590.0 | 268 | 243.1 | 1.1 | 581.9 | 63 | 51 | 166.5 | 117.5 | 198.3 | 5774 | 5013 |
| `bench/erc20_full.lithe` | 183 | 17.4 | 10533 | 1731.9 | 106 | 613.9 | 5.0 | 1718.4 | 99 | 91 | 674.6 | 325.6 | 444.1 | 9335 | 7382 |
| `scaling/n16.lithe` | 439 | 6.0 | 73130 | 34.5 | 12736 | 27.9 | 0.4 | 27.7 | 10 | 2 | 6.7 | 7.0 | 4.1 | 2559 | 2549 |
| `scaling/n32.lithe` | 871 | 7.6 | 115151 | 80.0 | 10890 | 58.0 | 0.7 | 71.7 | 10 | 2 | 21.0 | 17.9 | 6.6 | 4784 | 4774 |
| `scaling/n64.lithe` | 1735 | 15.3 | 113369 | 261.6 | 6632 | 192.8 | 1.8 | 250.6 | 10 | 2 | 72.0 | 80.1 | 13.8 | 9241 | 9231 |
| `scaling/n128.lithe` | 3463 | 25.1 | 138205 | 1122.9 | 3084 | 842.5 | 8.2 | 1101.8 | 10 | 2 | 268.9 | 475.6 | 31.7 | 18136 | 18126 |
| `scaling/n256.lithe` | 6919 | 70.5 | 98142 | 7407.3 | 934 | 6041.3 | 21.1 | 7364.6 | 26 | 4 | 1680.4 | 3403.3 | 97.0 | 42522 | 42512 |

`erc20_full` at one thread: wall 1.732 s, `/usr/bin/time` wall 1.73 s, CPU 1.72 s, peak RSS 121 MB. Sixteen threads bring that wall to 0.614 s. The search is still the whole cost (99 emits, 91 finishes, check 5 ms).

Per-line `promote`+`optimize` from the 439-line ladder to the 1735-line ladder is 2.8×. Phase 3's exit test wants that ratio ≤ 1.5. At N = 256 the search no longer stays at 10 emits / 2 finishes (26 and 4), and the backend is 7.36 s.

Gas is the in-crate meter, all 45 `bench/run.py` suites, outcomes included. A suite's `runtime_bytes` sums every contract it deploys, so it is not the single-file artifact when the suite deploys more than one.

| suite | runtime bytes | deploy gas | gas | steps | ok | revert |
|---|---:|---:|---:|---:|---:|---:|
| `counter` | 198 | 96234 | 188814 | 7 | 6 | 1 |
| `solady_erc20` | 1395 | 354803 | 1371033 | 45 | 33 | 12 |
| `uniswap_v2` | 10526 | 2677002 | 5295906 | 139 | 100 | 39 |
| `erc1155` | 6393 | 1668104 | 4968746 | 104 | 57 | 47 |
| `erc20_full` | 8204 | 2120779 | 6789562 | 148 | 106 | 42 |
