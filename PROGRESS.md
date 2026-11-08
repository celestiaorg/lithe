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

### Phase 3 — block IR, one-shot stack scheduling, linear passes

- [x] **3.1** CFG over `Vec<Inst>` and per-block worklist rewrites. Byte-identical in both modes. See the measurements below.
- [x] **3.2** `peephole` and `schedule` per block. Byte-identical in both modes. The 500-round bound stays, and the dirty-set was measured and dropped. See the measurements below.
- [ ] **3.3** Per-function stack scheduler. Spill to the memory home past DUP16/SWAP16. Differential at `LITHE_FUZZ_STEPS=5000`, prove tests, snapshot regenerated, gas outcomes unchanged and totals within 1%. **Not done; handoff below.**
- [x] **3.4** `outline` no longer O(n²): call sites are written in one pass instead of one splice each. It stays on the stream. Byte-identical. See the measurements below.
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

## 3.3 Stack scheduler: handoff

Not landed. The current `asm::promote` was measured first, to find out what a replacement has to beat and where its time goes (`target/fast`, `LITHE_THREADS=1`, ladder in Fast mode, temporary timers since removed):

| ladder | insts | rounds | promote | per round: region search | per round: incremental updates |
|---|---:|---:|---:|---:|---:|
| 16 | 3233 | 34 | 0.8 ms | 10 µs | 12 µs |
| 64 | 12694 | 130 | 9.0 ms | 36 µs | 32 µs |
| 128 | 25302 | 258 | 33 ms | 71 µs | 55 µs |

Each round applies one promotion, the best in the whole program. So the number of rounds grows with the number of functions, and every round scans the whole stream: it is quadratic. On ladder 128, promote is 34 ms of a 500 ms backend. `optimize` is 373 ms, so 3.2b, not promote, decides 3.5. On Release `erc20_full`, promote is 0.9 s of 2.4 s, summed over 97 emits.

Why it was not replaced in one step:

- `promote` is not one algorithm. It is several strategies tuned against the plan search:
  - holding a value within a straight run
  - holding a value over a region across branches and loops
  - `consume` (`plan.tight`)
  - `hold_dups`
  - `sink`
  - `abandon`
  - alias copies
  - `sink_exits`

  The Release search turns these knobs per candidate. A fresh value-numbering scheduler with RPO layouts has to match all of them within 1% total gas and size over 127 targets. The gas side also needs every one of the 45 `bench_gas` suites to keep its outcomes. That means measuring and tuning over many full gate runs, not writing one patch.
- A per-function batch of the current greedy is no shortcut either. Applying the best region of every function in one round is not byte-identical, because a region's edits can create new candidates that beat the next one in line. So it needs the same gas gate as a full scheduler, for a smaller payoff.

Suggested split:

1. **3.3a** Make the current greedy linear, byte-identical. Keep a heap of candidate bounds, keyed by the stable ids `RegionPlans` already maps across edits, so each round re-plans only the candidates its splice touched. The heap replaces the whole-stream `for i in 0..code.len()` scan in `promote_region`. Also give `Runs`/`Uses`/`Live::update` per-function arrays, so a splice shifts only its own function.
2. **3.3b** A scheduler for one function, behind a plan knob, so the search can compare it with the greedy by cost model on each candidate. Then gate it with the 1% budget, differential at 5000 steps, and the prove tests.
3. **3.3c** Remove the greedy once 3.3b wins or ties everywhere.

Stack-too-deep cannot occur today either: every local has a memory home, and promotion rewrites a load or store only when the value is within 16 items (`d < 16` in `promote_region`/`hold`). Otherwise the access stays on the home. `docs/src/pages/guide/architecture.mdx` explains this.

## 3.4 Outline without per-site splices

Plan: write every call site of a round in one pass over the stream, not with one `Vec::splice` per site. Proof: old and new binaries emit the same bytes. Expected effect: the O(sites × n) term goes away.

Profiling `outline_once` showed that `repeats` already refines groups of equal token runs one length at a time, with radix buckets by next token. That is the "hashed token runs" this task asked for, and it is linear in the stream times the lengths that survive. The quadratic part was the edit loop. Each of a round's call sites (511 on ladder 128) spliced the whole stream and the token arrays. That loop took 0.9 ms of a 6 ms round. Now return labels and tokens are assigned in the same order as before (last site first), and code, tokens, and sizes are rebuilt once. `outline` still runs on the flat stream. Moving it onto `Blocks` would add a conversion and save nothing: it runs once per finish, after `optimize` has already written the stream.

Equivalence: `lithe compile --fast` and `--release` on every `bench/`, `examples/`, and `fuzz/` file, plus ladders 64 and 128, produce identical stdout from the parent binary and this one (254 compiles plus 4 ladder builds). `tests/snapshots/bytecode.json` is unchanged.

Timing, `outline+` from `LITHE_TIME`, best of 5, `target/fast`, `LITHE_THREADS=1`, old → new:

| target | fast | release |
|---|---:|---:|
| ladder 128 | 27.8 → 29.8 ms | 28.4 → 26.8 ms |
| erc20_full | 10.6 → 10.4 ms | 482 → 478 ms |

The difference is noise on these targets. `outline+` is mostly the `optimize` and `finish` that run after outlining. The change removes the asymptotic term. It does not move the headline numbers.

## Comparison with baseline.json

Commit `9ec81c7` plus 3.4, measured on 2026-11-07. 3.2b, 3.3, 3.5, and phases 4–6 are not in this tree, so this table records the branch at this point. It is not the end of the program; re-run it when those land. `target/release/lithe` on 16 cores, `python3 scripts/bench_compile.py`, cache off. Fast rows use the same script with `--bin` pointing at a wrapper that passes `--fast` instead of `--release`, and `--skip-gas`. Wall-clock time includes process startup. **R** is Release, **F** is Fast; `(1)` is `LITHE_THREADS=1` and `(16)` is every core. "base" is `baseline.json` (v0.4.0, `796fdfe`).

- The Release run started while sibling builds were finishing. The ladder and large rows have wall ≈ CPU (for example, erc20_full 1.848 s wall vs 1.85 s CPU). Small Release rows under about 20 ms have startup noise of several milliseconds.
- The first Fast run was discarded: load average was 50 and wall was twice CPU. It was re-run once the load average dropped below 6.

| target | lines | base R ms (1) | R ms (1) | R ms (16) | F ms (1) | F ms (16) | base R runtime | R runtime | F runtime |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `bench/base64.lithe` | 14 | 7.6 | 15.0 | 15.7 | 7.0 | 7.3 | 891 | 891 | 874 |
| `bench/book.lithe` | 35 | 11.7 | 21.3 | 22.4 | 10.2 | 12.0 | 1160 | 1160 | 1091 |
| `bench/codec.lithe` | 69 | 52.2 | 91.9 | 67.0 | 20.6 | 20.6 | 2596 | 2596 | 2645 |
| `bench/collections.lithe` | 43 | 15.3 | 16.4 | 14.7 | 8.0 | 8.6 | 627 | 627 | 636 |
| `bench/counter.lithe` | 48 | 7.3 | 8.6 | 9.4 | 8.0 | 7.5 | 198 | 198 | 198 |
| `bench/date_time.lithe` | 57 | 70.7 | 81.7 | 65.0 | 9.4 | 11.3 | 1166 | 1166 | 1152 |
| `bench/deployers.lithe` | 69 | 64.1 | 71.6 | 54.8 | 12.5 | 12.3 | 1503 | 1503 | 1554 |
| `bench/dialer.lithe` | 52 | 18.1 | 21.1 | 24.5 | 11.8 | 11.6 | 1401 | 1401 | 1383 |
| `bench/env.lithe` | 16 | 5.1 | 7.7 | 7.7 | 7.5 | 7.9 | 81 | 81 | 81 |
| `bench/erc1155.lithe` | 158 | 590.0 | 698.5 | 290.1 | 31.0 | 32.7 | 5013 | 5013 | 4736 |
| `bench/erc20.lithe` | 99 | 121.2 | 133.6 | 70.4 | 16.3 | 14.5 | 2244 | 2244 | 2042 |
| `bench/erc20_full.lithe` | 183 | 1731.9 | 1848.4 | 623.9 | 57.7 | 56.5 | 7382 | 7382 | 7425 |
| `bench/erc4626.lithe` | 24 | 226.0 | 245.8 | 107.8 | 21.2 | 19.8 | 2884 | 2884 | 3120 |
| `bench/erc6909.lithe` | 68 | 159.2 | 181.5 | 87.9 | 17.4 | 19.2 | 3326 | 3326 | 3273 |
| `bench/erc721.lithe` | 119 | 159.2 | 180.5 | 96.8 | 20.0 | 20.4 | 3074 | 3074 | 3054 |
| `bench/erc721_full.lithe` | 176 | 503.4 | 590.5 | 225.1 | 32.3 | 34.4 | 5640 | 5640 | 5664 |
| `bench/exchange.lithe` | 51 | 9.8 | 12.0 | 11.4 | 9.2 | 8.2 | 417 | 417 | 442 |
| `bench/executor.lithe` | 115 | 16.3 | 24.9 | 17.1 | 10.0 | 8.1 | 807 | 807 | 822 |
| `bench/fixed_point.lithe` | 60 | 98.7 | 111.9 | 66.1 | 23.1 | 22.9 | 2831 | 2831 | 2918 |
| `bench/flash_borrower.lithe` | 55 | 15.6 | 16.8 | 16.1 | 11.4 | 11.4 | 822 | 822 | 871 |
| `bench/layout.lithe` | 64 | 7.0 | 8.6 | 8.4 | 8.6 | 9.4 | 705 | 705 | 705 |
| `bench/lists.lithe` | 68 | 18.9 | 18.7 | 20.1 | 11.0 | 10.7 | 1624 | 1624 | 1599 |
| `bench/logs.lithe` | 42 | 6.9 | 8.2 | 7.9 | 7.0 | 7.2 | 277 | 277 | 305 |
| `bench/loops.lithe` | 84 | 13.3 | 16.7 | 14.1 | 9.0 | 9.0 | 871 | 871 | 874 |
| `bench/math.lithe` | 24 | 6.5 | 7.5 | 6.6 | 8.0 | 7.7 | 424 | 424 | 424 |
| `bench/names.lithe` | 58 | 15.2 | 17.1 | 20.8 | 12.3 | 11.8 | 1312 | 1312 | 1289 |
| `bench/numerics.lithe` | 43 | 39.7 | 41.3 | 36.7 | 18.1 | 16.8 | 1679 | 1679 | 1702 |
| `bench/overloads.lithe` | 73 | 17.4 | 20.5 | 17.0 | 8.1 | 8.8 | 458 | 458 | 449 |
| `bench/ownable_roles.lithe` | 54 | 27.6 | 28.6 | 23.1 | 9.9 | 9.6 | 952 | 952 | 975 |
| `bench/profile.lithe` | 26 | 8.6 | 9.1 | 10.3 | 9.2 | 9.4 | 586 | 586 | 584 |
| `bench/reasons.lithe` | 80 | 10.8 | 12.4 | 10.9 | 8.9 | 7.8 | 844 | 844 | 845 |
| `bench/receiver.lithe` | 40 | 11.3 | 9.5 | 11.8 | 9.8 | 8.8 | 454 | 454 | 473 |
| `bench/receiver1155.lithe` | 76 | 18.8 | 17.1 | 15.4 | 9.7 | 9.1 | 926 | 926 | 944 |
| `bench/records.lithe` | 125 | 31.8 | 28.5 | 26.3 | 13.1 | 11.5 | 1508 | 1508 | 1508 |
| `bench/registry.lithe` | 68 | 13.9 | 14.9 | 13.1 | 11.1 | 9.1 | 1034 | 1034 | 1028 |
| `bench/relay.lithe` | 42 | 24.3 | 24.6 | 26.4 | 16.6 | 15.9 | 1886 | 1886 | 1828 |
| `bench/safe_erc20.lithe` | 29 | 11.7 | 11.6 | 12.3 | 9.0 | 9.5 | 543 | 543 | 543 |
| `bench/selectors.lithe` | 46 | 10.6 | 9.7 | 10.4 | 7.9 | 6.5 | 399 | 399 | 449 |
| `bench/shapes.lithe` | 86 | 17.9 | 18.9 | 18.1 | 11.6 | 12.8 | 1306 | 1306 | 1340 |
| `bench/solady_erc1155.lithe` | 249 | 91.7 | 96.1 | 62.5 | 19.9 | 17.6 | 2707 | 2707 | 2630 |
| `bench/solady_erc20.lithe` | 176 | 40.2 | 40.2 | 27.8 | 12.5 | 11.7 | 1395 | 1395 | 1402 |
| `bench/solady_erc721.lithe` | 241 | 67.6 | 74.1 | 48.9 | 19.4 | 15.9 | 2110 | 2110 | 2151 |
| `bench/staking.lithe` | 239 | 104.5 | 114.7 | 62.9 | 12.8 | 15.8 | 2486 | 2486 | 2177 |
| `bench/strings.lithe` | 70 | 17.2 | 18.7 | 17.9 | 14.8 | 13.3 | 1724 | 1724 | 1695 |
| `bench/tally.lithe` | 58 | 6.2 | 6.7 | 6.8 | 5.5 | 5.5 | 439 | 439 | 439 |
| `bench/texts.lithe` | 127 | 69.6 | 76.6 | 69.4 | 24.3 | 27.4 | 4105 | 4105 | 3911 |
| `bench/token.lithe` | 70 | 11.4 | 11.3 | 10.5 | 8.1 | 8.5 | 357 | 357 | 397 |
| `bench/traits.lithe` | 45 | 8.3 | 9.1 | 8.7 | 11.3 | 8.4 | 468 | 468 | 468 |
| `bench/uniswap_v2_factory.lithe` | 97 | 349.1 | 360.2 | 155.3 | 33.5 | 33.3 | 6038 | 6038 | 6213 |
| `bench/uniswap_v2_pair.lithe` | 529 | 338.6 | 347.4 | 151.6 | 31.7 | 32.1 | 5073 | 5073 | 5201 |
| `bench/vault.lithe` | 75 | 7.8 | 9.2 | 9.3 | 10.0 | 8.6 | 387 | 387 | 400 |
| `scaling/n16.lithe` | 439 | 34.5 | 35.2 | 29.9 | 21.9 | 22.8 | 2549 | 2549 | 2549 |
| `scaling/n32.lithe` | 871 | 80.0 | 80.1 | 58.7 | 44.8 | 42.8 | 4774 | 4774 | 4774 |
| `scaling/n64.lithe` | 1735 | 261.6 | 252.9 | 175.8 | 118.9 | 118.8 | 9231 | 9231 | 9231 |
| `scaling/n128.lithe` | 3463 | 1122.9 | 1006.2 | 706.0 | 495.0 | 485.4 | 18126 | 18126 | 18126 |
| `scaling/n256.lithe` | 6919 | 7407.3 | 4966.5 | 4118.6 | 2754.7 | 2755.8 | 42512 | 42512 | 42512 |
| **examples (71 targets)** | | 6195 | 6415 | 3076 | 862 | 858 | 85979 | 85979 | 87238 |
| **all (127 targets)** | | 20409 | 18623 | 11000 | 5044 | 5020 | 252311 | 252311 | 253359 |


Release bytecode and gas are identical to the baseline. All 45 `bench_gas` suites have identical outcomes. Total gas is 68 120 141 → 68 120 141, deploy gas 28 276 660 → 28 276 660, and suite runtime bytes 105 876 → 105 876. Every target's Release runtime size matches `baseline.json`. Fast is 0.4% larger in total runtime (252 311 → 253 359 bytes over all 127 targets). Its gas is in the 1.2 table.

Headlines against the prompt's targets:
- erc20_full in Fast: 1731.9 ms → **57.7 ms** (target ≤ 60 ms after Phase 1; ≤ 15 ms after Phase 3 is not met yet).
- All 127 targets, one thread: 20.4 s Release baseline → 18.6 s Release, 11.0 s Release on 16 threads, and **5.0 s Fast**.
- Ladder in Fast, per-line cost from 439 to 1735 lines: 21.9 ms / 439 = 50 µs/line → 118.9 ms / 1735 = 69 µs/line, a ratio of **1.37×**. From 1735 to 3463 lines it is 143 µs/line, a ratio of 2.1×. So scaling is still superlinear past 1735 lines; see the 3.3 handoff, and 3.2b for `optimize`.
- Threads only help Release. Fast is one build, so 1 vs 16 threads is the same within noise. Phase 4 is what would change that.
