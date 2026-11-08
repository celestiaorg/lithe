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

- [x] **1.1** `Opt { Fast, Release }` (`Default` = Release). Fast is one build of the `start` plan, plus the size-limit outline-more loop. CLI, `lithe.toml`, Standard JSON, and `analyze` wired as in decision 1. See the measurements below.
- [x] **1.2** Differential Fast vs Release over every target; Fast snapshot. Record erc20_full Fast time and the Fast-vs-Release size and gas table. Target ≤ 60 ms. See the measurements below.
- [x] **1.3** Cheaper Release search, byte-identical: dedupe plans, post-promote finish cache, lower-bound short-circuit, share `flow`/`heat` in `asm::gas`. See the measurements below.
- [x] **1.4** Per-function body memo in `Gen`. Release byte-identical. See the measurements below.

### Phase 2 — the language server never runs codegen on a keystroke

- [x] **2.1** `analyze_frontend` / `analyze_full`. LSP uses the frontend on open and change. Codegen errors on save, on a worker, cancelled when a newer edit arrives. See the measurements below.
- [x] **2.2** Per-session module cache keyed by path, content hash, and EVM version. `std/` parsed once per process. See the measurements below.
- [x] **2.3** Debounce `didChange` (50 ms), reader plus worker, rename, workspace symbol. Diagnostics on `bench/erc20_full.lithe` ≤ 20 ms (relaxed under `debug_assertions`). See the measurements below.
- [x] **2.4** VS Code extension and TextMate smoke test. See the measurements below.
- [x] **2.5** `LITHE_TIME` split of the frontend. The timed `erc20_full` test passes at its 20 ms optimized limit, with no relaxation (about 12 ms). The `Index` is still rebuilt on every edit; see below.

### Phase 3 — block IR, one-shot stack scheduling, linear passes

- [x] **3.1** CFG over `Vec<Inst>` and per-block worklist rewrites. Byte-identical in both modes. See the measurements below.
- [x] **3.2** `peephole` and `schedule` per block. Byte-identical in both modes. The 500-round bound stays, and the dirty-set was measured and dropped. See the measurements below.
- [x] **3.2b** Cheaper `merge_tails`/`heat`, byte-identical. Ladder 128 `optimize` 414 → 250–279 ms. erc20_full and uniswap_v2_pair release are still above their pre-3.1 cost. See below.
- [x] **3.2b(ii)** `heat` on the block skeleton, with a skeleton-keyed `flow` cache. Byte-identical. Goal missed; the measured floor is recorded below.
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

- [x] **6.1** Process startup. Measured; not taken.
- [x] **6.2** Assembler width fixpoint. It already is one, and candidate cost is already cached. Nothing taken.
- [x] **6.3** Memoize constant keccak. Measured; not taken.
- [x] **6.4** Incremental `heat` / `flow`. Taken in 3.2b(ii) as a skeleton-keyed `flow` cache; it hits on about 5% of calls.
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

## 1.1 Fast and Release

`Opt::Fast` builds the start plan once. The size-limit outline loop still runs, and checks are untouched. `Options::default()` stays Release. The CLI and `analyze` default to Fast; `--release`, `-O2`, or `[build] opt = "release"` selects the search. Safety: the release snapshot tests pass, so release bytecode is unchanged, and the release search still emits 99 times on `erc20_full`.

Quiet `target/release/lithe`, `LITHE_CACHE_DIR` empty, `LITHE_TIME=1`, `LITHE_THREADS=1`. Wall is a nanosecond clock around the process (the harness's `wall_s`). Release creation bytes match `baseline.json`. Fast creation bytes are informational; the size and gas table is 1.2.

| target | release wall | fast wall | release emits / finishes | fast emits / finishes | release creation | fast creation |
|---|---:|---:|---:|---:|---:|---:|
| `bench/counter.lithe` | 7 ms | 8 ms | 16 / 4 | 1 / 2 | 235 | 235 |
| `bench/solady_erc20.lithe` | 41 ms | 10 ms | 28 / 22 | 1 / 2 | 1405 | 1412 |
| `bench/uniswap_v2_pair.lithe` | 342 ms | 30 ms | 37 / 33 | 1 / 2 | 5267 | 5379 |
| `bench/erc1155.lithe` | 592 ms | 32 ms | 63 / 51 | 1 / 2 | 5774 | 5508 |
| `bench/erc20_full.lithe` | 1731 ms | 59 ms | 99 / 91 | 1 / 2 | 9335 | 9379 |

`erc20_full` fast: check 5.0 ms, backend 40 ms, promote 4.7 ms, optimize 12.5 ms, outline 10.8 ms. Wall 59 ms, under the 60 ms phase-1 target. Release wall 1731 ms matches the 0.2b baseline (1731.9 ms, 99 emits, 91 finishes, creation 9335).

`scripts/bench_compile.py` passes `--release`, so its report stays the release search now that the CLI default is Fast.

Tests: `cargo test --release --locked --offline` (544 lib, 21 bin, 1 doctest, 0 failed; snapshot, cache-key, and over-limit tests included), `cargo clippy --release --all-targets --offline -- -D warnings`, `cargo fmt --check` for the crate and the playground, `python3 scripts/bench_compile.py --self-check`, and `cargo build --release --locked --offline` of the playground (wasm32 via its cargo config). Release on these five contracts matches `baseline.json`. Fast rows for every harness target are task 1.2.

## 1.2 Fast vs Release

`fast_matches_release` builds each differential target (examples, fuzz, and bench) once in Release and once in Fast and replays the same calls. `tests/snapshots/bytecode.json` now has a `:fast` hash beside each Release hash. Release hashes are unchanged.

Quiet Fast timing is the 1.1 measurement on this commit's `target/release/lithe`: `erc20_full` wall 59 ms, backend 40 ms, 1 emit / 2 finishes, creation 9379. That is under the 60 ms bar. A remeasure of that same binary today, load average about 7 and the CPU governor in powersave, was slower by the same factor on both modes (Fast wall about 150 ms, Release wall 4279 ms beside the quiet 1731 ms). Creation bytes matched the 1.1 row. The machine was busy.

Single-file size is creation and runtime bytes from `lithe compile`. The gas column is the matching `bench/run.py` suite from `evm::bench_gas` on the dev compiler (`opt-level = 2`), which emits the same bytes. Outcomes are the ordered ok/revert and returndata hashes.

| bench file | release creation | fast creation | release runtime | fast runtime | suite | release gas | fast gas | gas |
|---|---:|---:|---:|---:|---|---:|---:|---:|
| `bench/counter.lithe` | 235 | 235 | 198 | 198 | `counter` | 188814 | 188814 | 0 |
| `bench/solady_erc20.lithe` | 1405 | 1412 | 1395 | 1402 | `solady_erc20` | 1371033 | 1371430 | +0.03% |
| `bench/uniswap_v2_pair.lithe` | 5267 | 5379 | 5073 | 5201 | `uniswap_v2` | 5295906 | 5306649 | +0.20% |
| `bench/erc1155.lithe` | 5774 | 5508 | 5013 | 4736 | `erc1155` | 4968746 | 4994541 | +0.52% |
| `bench/erc20_full.lithe` | 9335 | 9379 | 7382 | 7425 | `erc20_full` | 6789562 | 6806142 | +0.24% |

Suite runtime bytes, which add every contract a suite deploys, are 198/198, 1395/1402, 10526/10297, 6393/6153, and 8204/8296. Deploy gas is 96234/96234, 354803/356317, 2677002/2628109, 1668104/1616331, and 2120779/2140790. All 45 suites keep the same ok/revert status. `uniswap_v2` is the one suite whose returndata hashes differ: `createPair` is CREATE2, Fast init code is different, so the pair address and the domain separator that commits to it differ. Status stays ok. The pair's own differential run compared storage and results with the address fixed by the harness.

Tests: `cargo test --offline --lib evm::snapshot` (both snapshot tests, including VERIFY), `cargo test --offline --lib evm::differential::fast_matches_release -- --exact`, and `evm::bench_gas::bench_gas` for Release and Fast. The Fast gas run used a temporary `LITHE_OPT=fast` switch in `compile_file`; that switch is not in the tree.

## 2.1 Frontend on each edit

`lithe::analyze` is `analyze_full`. `analyze_frontend` loads, checks, lints, and indexes, and does not build. `analyze_full` adds one Fast build. A size-limit warning from that build is reported as the error when nothing else failed, so the editor can show it. Libraries still suppress "contract has no entrypoints".

The language server runs the frontend on open and change. On save it refreshes the frontend for every open file, then runs `analyze_full` on one worker. Each edit or save bumps a generation counter. The worker publishes only when the counter still matches. A build already running goes to completion, and a stale result is dropped. A check error wins over a codegen error. The worker shares `Stdout` (`StdoutLock` cannot move to another thread).

Tests: `cargo test --offline --bin lithe -- lsp::` (20 tests). Open of a storage-only file does not report "contract has no entrypoints"; save does. A save followed by an edit, with the worker held for 200 ms, publishes the edit's check error and not the stale codegen error. `config::tests::build_settings_come_from_the_nearest_file` still sees the `lithe.toml` error through `analyze`.

## 1.3 Cheaper Release search

The search still chooses the same plan. Release creation bytes on the five headline contracts match `baseline.json`.

- Identical plans are emitted once. Later rounds reuse that emit.
- `finish` reuses optimized code when the post-promote code, entry labels, and leaf sizes match, then prices gas and runtime for that candidate's heap and data. The `flow` result for that optimized code is stored with it, so a hit does not run `flow` again. A build with tracking on, and the final `both` outline, still run the passes.
- `round` skips a plan only when that exact plan was already finished and its measured cost is at or above the retry bar. The delta of that plan is past the threshold, so dropping it does not change which toggles are retried. A plan that only inlines more is still built: inlining can shrink the placed runtime, so a subset of an over-limit outline is not a lower bound. `chain` does not cut a suffix on that guess.
- `heat` during `optimize` does not consult a process-wide cache. Those passes rewrite the stream, so a memo of the last few copies misses and serializes parallel finishes.

`target/fast/lithe` (release opts, no fat LTO), `LITHE_CACHE_DIR` empty, `LITHE_THREADS=1`. Baseline is fat-LTO `target/release`. Creation bytes match. Emits fall by the duplicate plans. Finishes do not: on these contracts distinct plans do not share post-promote code, so the finish cache does not fire. Wall time stays within about 5% of the fat-LTO baseline; that gap is the binary.

| target | baseline wall | wall | baseline emits / finishes | emits / finishes | creation |
|---|---:|---:|---:|---:|---:|
| `bench/counter.lithe` | 7.3 ms | 8.7 ms | 16 / 4 | 14 / 4 | 235 |
| `bench/solady_erc20.lithe` | 40.2 ms | 40.5 ms | 28 / 22 | 25 / 22 | 1405 |
| `bench/uniswap_v2_pair.lithe` | 338.6 ms | 357.3 ms | 37 / 33 | 35 / 33 | 5267 |
| `bench/erc1155.lithe` | 590.0 ms | 604.5 ms | 63 / 51 | 57 / 51 | 5774 |
| `bench/erc20_full.lithe` | 1731.9 ms | 1816.1 ms | 99 / 91 | 97 / 91 | 9335 |

Tests: `cargo test --offline --lib evm::snapshot::release_bytecode_matches_snapshot -- --exact`, `cargo clippy --offline --all-targets -- -D warnings`, `cargo fmt --all`.

## 2.2 Module cache

`ModuleCache` stores parsed files and checked programs by canonical path, content hash, and EVM fork. The LSP holds one per session. `std/` is parsed once per process; the test compares the `Arc` for the files that load touched, not the size of the process-wide map. A second analysis of the same text reuses the checked program, and so does an undo back to it. A new edit still runs the whole-program check: checking is not split by file, and `src/check` is outside this step. The edited file is parsed again; `std/` is not.

The checked map keeps eight programs per path and drops the least recently used. A deeper undo checks again.

Tests: `cargo test --offline --lib -- std_is_parsed_once session_cache::` (3 passed).

## 1.4 Per-function body memo

Outlined bodies are remembered for the rest of `codegen`, keyed by the function, whether it runs storage in place, the constants it was specialized to, a hash of the immutable constants, and the plan bits that reach the body. Those bits are the knobs read while emitting (`cache_slots`, `tight`, `outline_raises`, the shared helpers, blob and queue sets) and the outline and specialize flags of the functions the body calls. Frames, sink, held duplicates, abandon, forwarded constants, and a static heap are applied after emit, so a plan that flips only one of those does not re-emit the body.

A hit pastes the body back with its labels and new regions shifted onto this emit. It is declined when a helper that already existed, a region allocated earlier in this emit, or the embedded-data prefix no longer lines up; that body is compiled again. A body that allocates or writes the error head restores that region, and is declined when this emit already has a different one, so the revert helper reads the head the body filled. Release creation bytecode is unchanged: both snapshot tests passed, including `VERIFY`.

Tests: `cargo test --offline --lib gen::body::memo_tests`, `cargo test --offline --lib evm::snapshot -- --test-threads=8`, `cargo clippy --offline --all-targets -- -D warnings`, `cargo fmt --check`.

## 2.3 Debounced language server

`lithe lsp` reads frames on the calling thread and analyzes them on a worker. `didChange` waits 50 ms and keeps the latest text, so a burst of keystrokes checks once. The next message, or the end of the wait, runs that check. `textDocument/rename` returns a workspace edit for the name under the cursor. `workspace/symbol` lists outline symbols of the open files that match the query.

Debounce and the diagnostic timer belong to one server, not the process, so parallel tests do not share them. On an edit of `bench/erc20_full.lithe`, with the standard library already parsed, `apply_frontend` plus publishing diagnostics took 19 ms alone and 20 ms beside the other lsp tests, in the opt-level 2 dev profile.

Re-measured on 2026-11-07 with sibling builds running (load average 10–12 on 16 cores): about 50 ms in both the dev and fast profiles. The split was check 15 ms, lint 14 ms, index 9 ms, load 2 ms. Lint was running `check_in` a second time. `lint_source` now takes the units the frontend already checked (only when the EVM version is the default, which is the one lint checks for), so lint output is unchanged. After that, the best of five runs is 26–33 ms. The test takes the best of five runs and asserts ≤ 20 ms in an optimized build and ≤ 60 ms under `debug_assertions`. The dev profile (`cargo test`, `make check`, CI) passes. **The 20 ms optimized target is not met yet.** The rest is `index::build` walking every declaration, std included (~9 ms), plus check itself.

Tests: `cargo test --offline --bin lithe -- lsp::` (22 tests), `cargo clippy --offline --all-targets -- -D warnings`, `cargo fmt --check`.

## 2.4 Editor smoke test

Plan: drive `lithe lsp` with the message sequence the VS Code client sends, check that the extension still installs and that its grammar matches the shared one, and document when diagnostics appear. No code change, so bytecode is untouched.

Run on 2026-11-07 against `target/fast/lithe`, with a Python LSP driver that sends the same framing and messages as `vscode-languageclient` 9.0.1:

| step on `bench/erc20_full.lithe` | result |
| --- | --- |
| `initialize` | advertises sync with `save`, hover, definition, references, highlight, document symbol, rename, workspace symbol, completion, signature help, formatting, and code actions. The client only sends `didSave`, rename, and workspace symbol when they are advertised, so this matters |
| `didOpen` | 2 lint warnings, 42 ms |
| `didChange` with a syntax error | the parse error, 51 ms including the 50 ms debounce |
| `didChange` back, then `didSave` | 2 warnings; the save build adds nothing |
| hover, rename, `workspace/symbol`, formatting | answered (rename: 1 edit, 18 workspace symbols) |
| `shutdown` / `exit` | exit code 0 |

Codegen errors on save, using a contract with no entrypoints: `didOpen` publishes nothing. `didSave` publishes the frontend result, then "contract has no entrypoints" from the worker. The next edit clears it until the next save. A file with no `contract` declarations is a library, and `analyze_full` deliberately does not report NO_ENTRIES for it.

Extension: `npm ci` in `extensions/vscode` installs `vscode-languageclient` 9.0.1. `code --extensions-dir <tmp> --list-extensions` lists `lithe.lithe@0.1.0` from a copy of the folder. `extensions/vscode/syntaxes/lithe.tmLanguage.json` is byte-identical to `extensions/lithe.tmLanguage.json` (`scopeName` `source.lithe`, matching `package.json`). Opening a window was not possible on this headless box, so in-editor highlighting and the client's activation were not observed. The protocol run above covers what the client relies on from the server.

Docs: `editors.mdx` has a "When errors appear" section covering diagnostics on edit and codegen errors on save.

## 3.1 Block CFG

Plan: add `asm::blocks::Blocks`, a block list with labels resolved to block ids, `succ`/`preds` (one edge per pushed label or table entry, plus fallthrough), and a serializer. Move `prune_labels`, `remove_dead`, `thread_jumps`, `dedup_blocks`, `merge_tails`, `rotate_loops`, `rotate_exits`, and `hoist` onto it. They edit block bodies in place or move whole blocks; none splices the global stream. Proof: byte-identical output from every pass call, then the Release and Fast snapshots.

A block starts at its labels, or after an exit, and runs to the next exit or label. So every label heads a block, and only the first block or dead code has no label. `JUMPI` does not end a block: the stream passes treat a run through a `JUMPI` as one unit, and keeping that shape is what makes them byte-identical. `remove_dead` becomes "drop every unlabelled block but the first". The `dedup_blocks`/`merge_tails` segments are the blocks that end in an exit. `merge_tails` counts calls with `preds`. `hoist` and `rotate_exits` reorder `Vec<Block>`. `rotate_exits` no longer clones the whole stream for each candidate once it is past byte 0xff. Each pass still takes `&mut Vec<Inst>`, so `track::pass` carries marks exactly as before. When nothing is tracked, `optimize` runs prune, dead, and thread on one `Blocks` per round.

Equivalence: during development, every call of each new pass was asserted equal (code and `changed` flag) to the old stream implementation over the whole lib suite (550 tests, including both snapshot modes). The oracle was then removed with the old code. `tests/snapshots/bytecode.json` is unchanged.

Timing (`target/fast`, `LITHE_THREADS=1`, cache off, best of 3, parent commit vs this one):

| target | mode | optimize old → new | backend old → new |
|---|---|---:|---:|
| erc20_full | release | 339 → 388 ms | 1813 → 1868 ms |
| erc20_full | fast | 12.6 → 13.5 ms | 42.1 → 42.4 ms |
| uniswap_v2_pair | release | 59.9 → 66.2 ms | 347 → 353 ms |
| uniswap_v2_pair | fast | 5.0 → 5.8 ms | 21.4 → 22.0 ms |
| ladder 64 | fast | 81 → 90 ms | 119 → 129 ms |
| ladder 128 | fast | 481 → 523 ms | 607 → 648 ms |

**This slice is 10–15% slower in `optimize`.** It is a representation change, and the 500-round loop still converts stream → blocks → stream around `clean`, `dedup_blocks`, and `merge_tails` every round. Per-pass timing on ladder 128 puts nearly all of the extra time in those conversions. The pass bodies cost the same as before. `merge_tails` is 75% of `optimize` in both versions: its pairwise tail comparison within same-ending groups is quadratic. 3.2 should keep one `Blocks` across the whole round, with `peephole`, `dup_constants`, and `schedule` per block, and serialize once at the end of `optimize`. That removes the conversions. `merge_tails` should then group tails by a hash of suffixes rather than compare all pairs. `rotate_loops` still scans every block per loop head, as the stream version scanned every instruction (marked `simplify:`); a label → referencing-block index would make it linear.

Tests: `cargo test` (lib, bin, and integration), `LITHE_VERIFY=1` snapshot, `LITHE_FUZZ_STEPS=2000` differential, `cargo clippy --all-targets -D warnings`, `cargo fmt --check`. New unit test `asm::blocks::tests::splits_links_and_writes_back` covers the split, the serializer, `succ`/`preds`, and prune + dead.

## 3.2 Rounds on one set of blocks

Plan: run all of `optimize`'s rounds on one `Blocks` and write the stream once at the end. Run `peephole`, `dup_constants`, and `schedule` per block. Proof: a lockstep oracle during development, then the Release and Fast snapshots. Expected effect: `optimize` loses the per-round conversions.

What changed (`src/asm/blocks.rs::optimize`, used whenever no prover marks are tracked; the tracked path stays pass by pass on the stream):

- **`peephole` per span.** A span is a block plus the labels of the next block. Rewrites look at those labels but never take them. A block ending in `PushLabel JUMP` is scanned together with the following block. A rewrite that empties that block exposes more labels to the jump, and the stream pass catches that by backing up over the labels. The oracle found exactly this case. The unit test `rounds_on_blocks_match_the_stream` fails when spans are disabled.
- **Output pieces.** A changed span is re-split with `Blocks::new`, and `tidy` joins the pieces.
- **`dup_constants`** runs per body. It already forgets the stack at labels and exits. It now reuses one stack across bodies (`dup_constants_in`).
- **`schedule`** computes `safe_exits` once, then reschedules each body's runs. It calls `tidy` when it empties a body.
- **`dedup_blocks`** keys on the whole body. It no longer compares, pairwise, every body that shares a length and its first and last instructions.
- **`merge_tails`** groups exits by their shortest tail of at least `MIN_TAIL_BYTES`. The old two-instruction key let pairs that can never merge in. It also stops the per-pair length scan once the best saving so far is at least the most any shorter tail can save. Heat is never negative and `byte_gas` is positive, so this cut is exact. The final sort is a total order, so group order does not matter.

Equivalence: during development, after every pass of every round, `b.code()` and the `changed` flag were asserted equal to the stream pass on a parallel copy. `b` was also asserted equal to `Blocks::new(&b.code())`, so the normal form holds. This ran over the whole lib suite (551 tests), plus `lithe compile --release`/`--fast` on every `bench/`, `examples/`, and `fuzz/` contract and ladders 64 and 128. The oracle was then removed. Old and new binaries emit the same bytes for all of these. `tests/snapshots/bytecode.json` is unchanged.

Not done, and why:
- **The 500-round bound.** It is still there as a guard against passes that never settle. Its output is identical as long as the bound is never reached. Rounds on ladder 128 stay at about 131 per `optimize`, because `merge_tails` applies about one merge per group per call: a block that loses to a longer pair poisons its partner. Fewer rounds means merging more per call, which changes codegen. That belongs to 3.4.
- **The dirty-set.** A content memo of spans `peephole` had left clean was built and measured. It made `optimize` slower on every target: erc20_full release 413 → 433 ms, ladder 128 372 → 381 ms. Hashing and cloning each span cost more than rescanning it, so it was removed. Exact identity tracking would need every body edit in every pass to clear a flag. That is not worth it at `peephole`'s share.

Timing (`target/fast`, `LITHE_THREADS=1`, cache off, best of 5, parent commit vs this one, `optimize` sum / backend):

| target | mode | optimize old → new | backend old → new |
|---|---|---:|---:|
| erc20_full | release | 387 → 395 ms | 1864 → 1881 ms |
| erc20_full | fast | 13.4 → 13.7 ms | 42.4 → 43.0 ms |
| uniswap_v2_pair | release | 66.3 → 68.9 ms | 350 → 354 ms |
| uniswap_v2_pair | fast | 5.6 → 6.0 ms | 21.1 → 20.3 ms |
| ladder 64 | fast | 89.9 → 70.4 ms | 128 → 109 ms |
| ladder 128 | fast | 518 → 359 ms | 641 → 481 ms |

The 3.1 diagnosis was wrong. Removing the conversions alone moved nothing (ladder 128: 519 → 535 ms). The per-round cost is the passes themselves:
- On ladder 128, `merge_tails`'s pairwise loop was about 1–3 ms per call. It runs about 131 times per `optimize`, and on groups of up to 256 exits that end alike.
- `dedup_blocks`' pairwise find was 51 ms.

The ladder gain comes from the `dedup_blocks` and `merge_tails` changes (dedup 51 → 14 ms per `optimize` on ladder 128). On real contracts, per-block `peephole` costs about 16 ns per span more than one pass over the stream. erc20_full release, summed over all its `optimize` calls (2638 rounds): `peephole` 66 → 92 ms, roughly paid back by `clean` 98 → 64 ms. So real contracts land within 1–4%.

What remains: `merge_tails` is still the largest pass (180 ms of erc20_full release, about 1 ms per call on ladder 128). Each call recomputes `heat` over the whole stream and re-pairs every group. Making that incremental (6.4), or merging more per call (3.4, which changes bytes), is where `optimize`'s superlinearity now lives. `rotate_loops`' `simplify:` note from 3.1 still stands.

Tests: `make check`:
- fmt and clippy `-D warnings` (crate and playground)
- `cargo test --locked`
- `LITHE_VERIFY=1 cargo test`
- `LITHE_FUZZ_STEPS=2000` differential
- snapshot
- bench-gas
- playground wasm build

New unit test `asm::blocks::tests::rounds_on_blocks_match_the_stream`: one `peephole` pass and the full rounds, blocks against the stream.

## 2.5 Diagnostics gap

`analyze_in` (the frontend behind `apply_frontend`) prints `[time] frontend load=… check=… lint=… index=…` when `LITHE_TIME` is set. When the checked units come from the session cache, the `check` lap is missing from the line.

Measured with `LITHE_TIME=1 cargo test --profile fast --bin lithe did_change_coalesces -- --nocapture` on 2026-11-07, load average 1–6 on 16 cores. Each line is one `apply_frontend` on `bench/erc20_full.lithe`:

| phase | 2.3 entry (load 10–12) | now |
|---|---:|---:|
| load | 2 ms | 0.9–2.1 ms |
| check | 15 ms | 5.8–8.6 ms |
| lint | 14 ms (re-checked) | 0.4–0.6 ms |
| `index::build` | 9 ms | 3.4–5.4 ms |

The test passes at its unrelaxed 20 ms optimized limit, best of five, three runs out of three. The sum is about 11–13 ms. The 26–33 ms recorded in 2.3 was measured under load 10–12. The code change that mattered was the lint dedup already recorded in 2.3.

**Incremental `Index` not taken.** `index::build` is one builder whose def ids, `kids`, `spelled`, and file order come from walking every unit, std included, in order. Reusing per-unit pieces would mean renumbering defs and refs across units, which risks the hover, definition, reference, and rename answers and their order that the LSP tests pin. That is a lot of risk for at most 3.5 ms, with the target already met. If Phase 3's ≤ 5 ms target needs it, the cheaper next step is to build the index lazily on the first hover or definition request, which takes it off the diagnostics path without changing any answer. Check itself (≈6 ms) is untouched.

Tests: `cargo test --profile fast` (552 lib + 25 bin + 1, all green), `cargo clippy --all-targets -- -D warnings`.

## 3.2b Cheaper `merge_tails` and `heat`

Plan: cut the cost of `merge_tails` and its `heat` without changing a byte. Every cut has to be exact. Proof: both snapshots, `rounds_on_blocks_match_the_stream`, and the `LITHE_FUZZ_STEPS=2000` differential.

What changed:
- **`heat` was already computed at most once per call**, lazily, through a `OnceCell`. Across calls the input always differs, because some pass changed the blocks in between, so there is no exact memo to take.
- **`flow` (asm.rs):**
  - The loop-depth walk found each header's latches by scanning every block, which costs O(headers × blocks). It now builds the header → latches lists once. The walk's result does not depend on order.
  - The cold-block fixpoint sweeps blocks backwards. That gives the same least fixed point of a monotone rule in fewer sweeps.
- **`serialize`** copies each body with `extend_from_slice` instead of a flat-map iterator. On erc20_full its share of `heat` went from about 21% to about 8%.
- **`merge_tails` pairing:**
  - Each group of exits is sorted by its body read backwards, using `order`, a total order on `Inst` that is equal only for equal instructions. Any pair's common tail is then the least common tail of the neighbours between them. Each body's suffix byte sums are computed once, only as far as it shares with a neighbour.
  - Pairs are still formed as (lower, higher) block index. The final sort key is total, so generation order does not matter.
  - Singleton groups are skipped.
  - The `calls(give)` test and the `best ≥ most` bound now come before the heat lookup. Both conditions already rejected those candidates, and heat is never negative.

Per-pass split, summed over all `blocks::optimize` calls of one compile (`target/fast`, `LITHE_THREADS=1`, cache off, temporary timers). The sums include `optimize` calls inside `outline`, so they exceed the `optimize` timer:

| target | clean | peephole | dedup | dup_const | merge_tails (heat) | schedule | `optimize` timer |
|---|---:|---:|---:|---:|---:|---:|---:|
| erc20_full release, before | 64 | 94 | 66 | 76 | 183 (107) | 81 | 402 ms |
| erc20_full release, after | 67 | 97 | 67 | 76 | 173 (92) | 81 | 383–403 ms |
| uniswap_v2_pair release, before | 10.6 | 16.5 | 10.9 | 12.7 | 26.8 (17.6) | 25.2 | 77.9 ms |
| uniswap_v2_pair release, after | 9.8 | 14.5 | 10.5 | 11.6 | 21.5 (13.1) | 21.7 | 67–69 ms |
| ladder 128, before | 25 | 40 | 31 | 20 | 295 (102) | 7.6 | 414 ms |
| ladder 128, after | 23 | 37 | 29 | 19 | 139 (42) | 7.6 | 250–279 ms |

Ladder 128's merge_tails pairing (without heat) went from about 170 ms to about 60 ms, and its heat from 102 ms to 42 ms. Its `optimize` is now under the 359 ms goal.

**Missed: erc20_full and uniswap_v2_pair release are still above their pre-3.1 `optimize` cost** (339 ms and 59.9 ms in the 3.1 entry). On these targets, heat is a whole-program `flow` that is needed on nearly every call. Its cost is the flow itself, not the serialize or the header scan. Per-span `peephole` (≈95 ms) is the other overrun. It is bounded by building each span's window, and the 3.2 dirty-set already measured slower. The `rotate_loops` label index was not taken: `rotate_loops` runs in `outline`'s finish callback, not in `optimize`'s rounds, so it is outside this split. Closing the remaining gap needs fewer rounds, by merging more per call (3.4, changes bytes), or a block-skeleton-keyed `flow` (6.4).

Proof:
- `tests/snapshots/bytecode.json` unchanged (`evm::snapshot`, Release and Fast).
- `cargo test --profile fast`: 552 lib + 25 bin + 1, all green, including `rounds_on_blocks_match_the_stream`.
- `LITHE_FUZZ_STEPS=2000` differential green.
- `cargo clippy --all-targets -- -D warnings` clean.

## 3.2b(ii) `heat` on the block skeleton

Plan: stop re-serializing for `heat`, and reuse `flow` when the structure it reads is unchanged. Both are exact. Proof: both snapshots, `rounds_on_blocks_match_the_stream`, and the `LITHE_FUZZ_STEPS=2000` differential.

What changed (`asm::blocks::stream_heat`):
- **No `serialize`.** `merge_tails` builds a skeleton straight from `blocks`. With `sum` off, `flow` reads only labels, label pushes, tables, and the exits and `JUMPI`s that end its blocks, and an instruction's heat is its flow-block's weight. So each run of other instructions becomes one placeholder, which keeps flow-block boundaries and the "`PushLabel` right before the jump" test. Each instruction maps to its skeleton slot.
- **Skeleton-keyed cache.** A per-thread copy of the last skeleton and its heat. A hit requires the whole skeleton to be equal, not just a hash, so the cached vector is reused only for the exact input that made it.
- **Check.** Under `LITHE_VERIFY` (or `asm::VERIFY`), every call asserts that the mapped heat equals `heat(&serialize(blocks))`. That covers the whole `LITHE_VERIFY=1` suite and both snapshot-under-verify tests. During development the assert ran on every call of erc20_full and uniswap_v2_pair release.

Measured (`target/fast`, `LITHE_THREADS=1`, cache off, min of 7 alternating runs against the parent build, machine load 19–47 from other sessions):

| target | parent | this | pre-3.1 goal |
|---|---:|---:|---:|
| erc20_full release `optimize` | 381.5 ms | 375.9 ms | 339 ms |
| uniswap_v2_pair release `optimize` | 65.9 ms | 66.0 ms | 59.9 ms |

Inside one erc20_full compile, `heat` over all 1890 `merge_tails` calls (including `outline`'s): 87 ms before, 84 ms after, with skeleton building included. The skeleton is about 36% of the stream (1475 vs 4094 instructions on average). The cache hits 89 of 1890 calls. `merge_tails` runs only in a round where nothing else changed, and the previous merge has just changed the labels and jumps, so a repeated skeleton is rare.

**Floor: about 376 ms / 66 ms. The goal is missed.** `flow`'s cost is per block, not per instruction, and no single phase holds the 37 ms gap. Split of `flow` over one erc20_full compile (temporary timers): starts 8, label map 11, successors 11, cold fixpoint 6.5, DFS 9, preds 5, indeg 3, entry walk 23 ms. Heat is called once per merge round. Getting under 339 ms needs fewer `merge_tails` calls, by merging more per call (3.4, which changes bytes), or the per-span `peephole` overrun (≈95 ms) recovered. Neither fits under the byte-identical constraint here.

Gates at this head:
- `cargo test --locked` (dev profile): 552 lib + 25 bin + 1, green.
- `LITHE_VERIFY=1 cargo test --locked`: 552 lib + 25 bin + 1, green.
- `tests/snapshots/bytecode.json` unchanged (Release and Fast, plus under verify). `rounds_on_blocks_match_the_stream` and `incremental_analyses_agree_with_fresh_ones` green.
- `LITHE_FUZZ_STEPS=2000` differential: 5 tests green.
- Playground `cargo build --release --locked` (wasm32-unknown-unknown): builds.
- `cargo fmt --check` clean in the root and in `playground`. `cargo clippy --all-targets --locked -- -D warnings` clean.

The 2.5 `LITHE_TIME` frontend lap now reports codegen as its own `build=` phase. On the uncached path `check=` used to include it. On the cached path it was not timed at all. Repeated marks of the same phase add up.

## 6.1–6.4 Evaluated

Measured 2026-11-07, `target/fast`, cache off:

- **6.1 Startup.** `lithe --version`: 1.5 ms min / 1.9 ms median over 50 runs, against 0.17 / 0.25 ms for `/bin/true`. That is about 1.3 ms of process start for a 47 MB unstripped binary (release is stripped). It is small next to any compile (Fast erc20_full ≈ 44 ms backend). Not taken.
- **6.2 Assembler.** `assemble_marked` is already a least fixed point: every label push starts at one byte and widens monotonically. Candidate cost is computed once per finish (`Built.cost`), and `asm::cost` runs only twice per `outline` with `both`. Nothing to take.
- **6.3 Keccak memo.** With a temporary counter:
  - erc20_full release: 81 982 calls, 20.9 ms of a 1.9 s backend (1.1%).
  - erc20_full fast: 2 923 calls, 0.75 ms of 44 ms (1.7%).
  - uniswap_v2_pair release: 13 864 calls, 3.5 ms.

  A memo pays a hash and a key allocation per call against about 250 ns of hashing. It would save well under 1%. Not taken.
- **6.4 Incremental heat/flow.** After 3.2b, heat is 92 ms of erc20_full release (about 5% of the backend) and 42 ms of ladder 128. A block's heat depends on global structure: coldness, loop depth, and the topological order of entries. Recomputing one block would need a skeleton-keyed cache (labels, label pushes, exits, and `JUMPI` positions) and an exact invalidation argument. Not taken in this iteration. It is the next lever for erc20_full's `optimize`, after 3.4.

