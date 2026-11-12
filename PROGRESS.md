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
- [x] **2.6** The index is built on the first request that needs it, not per edit. Diagnostics on erc20_full 12 → 6.5 ms. **The ≤ 5 ms target is missed:** `check` alone takes 5.3–5.8 ms. See below.

### Phase 3 — block IR, one-shot stack scheduling, linear passes

- [x] **3.1** CFG over `Vec<Inst>` and per-block worklist rewrites. Byte-identical in both modes. See the measurements below.
- [x] **3.2** `peephole` and `schedule` per block. Byte-identical in both modes. The 500-round bound stays, and the dirty-set was measured and dropped. See the measurements below.
- [x] **3.2b** Cheaper `merge_tails`/`heat`, byte-identical. Ladder 128 `optimize` 414 → 250–279 ms. erc20_full and uniswap_v2_pair release are still above their pre-3.1 cost. See below.
- [x] **3.2b(ii)** `heat` on the block skeleton, with a skeleton-keyed `flow` cache. Byte-identical. Goal missed; the measured floor (taken at machine load 19–47) is recorded below.
- [x] **3.2c** Fewer `merge_tails` calls: a block whose best partner is taken now takes its next-best free pair in the same call. Codegen change, gated and recorded in `## 3.2c`. `optimize` erc20_full Release 382.0 → 301.3 ms, ladder 128 Fast 251.1 → 31.0 ms (min of 7, load 2.0), and the pre-3.1 floor 3.2b(ii) owed is re-measured at load 1.6–2.1: erc20_full 340.4 → 306.3 ms, goal met; uniswap_v2_pair 57.8 → 62.4 ms, still 4 % over. Runtime bytes +0.072 % over 304 target-modes, transaction gas +0.0012 %, every step status unchanged. See below.
- [x] **3.3** Per-function stack scheduler. Spill to the memory home past DUP16/SWAP16. Differential at `LITHE_FUZZ_STEPS=5000`, prove tests, snapshot regenerated, gas outcomes unchanged and totals within 1%. Split into 3.3a–c. **The value-numbering scheduler itself is not taken (S48):** `promote` is 8.9 % of the Fast backend over all 51 `bench/` and 3–4 % on the ladder, so it moves no open target; see `## S48 3.3 closed: not taken`. **3.3b(ii) landed: promotion now plans every word's region once and applies every non-conflicting one per round, so rounds are 4 at every ladder size (was 34/130/258), `promote` is 49.6 → 12.0 ms on ladder 128, and runtime size is −0.027 % over the 272 target-modes (−0.153 % creation + runtime over the 13 whose code changes; the `Fast` increases are the batched start plan's price, not a search result). It is a plan knob (`Plan::batch`, on in the start plan, priced against off by the search).** 3.3a landed in part; 3.3b(i) was measured and not taken (+4.1 %/+4.6 % size). 3.3c was measured and not taken: batch loses to the greedy path on 22 of 1 140 Release on/off pairs, reproduced from the tree with `LITHE_PRICE_BATCH` (see `## S40 3.3c priced`).
- [x] **3.4** `outline` without its quadratic terms. What moved: call sites are written in one pass instead of one splice each (3.4), and the exact-copy pass now takes every non-conflicting run per round, as the parameterised pass already did (3.4b), so a pass runs a handful of rounds, not one per distinct run. What did not: `outline` itself stays on the flat stream, not on `Blocks`; `flow`/prefix sizes are still recomputed each round, measured at 10–12% of the `outline_once` loop and not worth an incremental cache. Final bytes unchanged in both modes; the exact pass's own output does differ on some targets (see 3.4b). Re-verified at `3a670f0`. See the measurements below.
- [x] **3.5** Ladder: per-line `promote`+`optimize` cost from 439 to 1735 lines ≤ 1.5×. **Met at 1.5×-or-better in both modes: 0.63× Fast, 0.90× Release** (min of 5; medians 0.59× and 0.87×). No new cut was needed — 3.2c and 3.3b(ii) landed the work after this table was written, and re-measuring on this tree shows the 1735-line rung 3.5–4.8× cheaper per line than when it was recorded at 42.9 (Fast) and 69.3 (Release) µs/line. The bar is met with margin while the superlinear term is not gone, only pushed out of the measured range: past 1735 lines Release still costs 1.30× and 1.81× more per line at 3463 and 6919. See `## S50 3.5 closed`.

### Phase 4 — parallelism inside one build

- [x] **4.1** Per-function parallel emit, schedule, and optimize. Deterministic join. Wasm stays single-threaded. Test `LITHE_THREADS=1` vs N. **Not taken (S23):** the emitter's per-body work, the only part that exists per function before `resolve` joins the stream, is 9.1 % of the Fast backend and 8.2 % of Release over 50 `bench/` files. Even with unlimited threads and a free join, that caps the speedup at 1.10×. The join would also have to relocate every piece of shared emitter state that `recall_body` relocates, including the 21 cases where it gives up today. See `## S23 4.1 closed: not taken`.
- [x] **4.2** Overlap sibling `check` and `route::abi` with codegen. Determinism test. **Landed (S24):** `compile` builds a file's sibling units on `gen::parallel_map` and returns them in declaration order. `sibling_units::pooled_build_matches_one_thread_in_order` checks the bytes, and factory's digests are identical at `LITHE_THREADS=1` and 16. No benchmark number moves, because `examples/factory.lithe` is the only file with two units. See `## S24 4.2`.

### Phase 5 — frontend hygiene and caching

- [x] **5.1** Identifier interner. **Measured and split: not doable in one slice.** Adding `Symbol`/`Names` and flipping `NameAt.name` alone breaks 184 sites in 19 files, 12 of them outside this slice, and the table has to be shared across merged files before any field can move. Split into 5.1a (table + determinism proof, **landed**), 5.1b (AST fields, **landed**) and 5.1c (the checker's maps, **landed**, S29): `Checker.named`, `Checker.domain_tys`, `Scope.vars` and `Checked.named`/`domain_tys` are keyed by `Symbol`, `route`/`index` sort on `Names::get` text so ABI and hover order is unchanged, and `check` on erc20_full is 5.83 → 5.67 ms (min of 25, interleaved A/B). Both snapshots and a 52 213-line diagnostic corpus unchanged. See `## 5.1 Interning: scope measured`, `## 5.1a The table`, `## 5.1b` and `## 5.1c`.
- [x] **5.2** `FileId` and byte `Span`. Diagnostics keep `line` and `column`. **Landed (S57, 5.2a):** every AST `line`/`col` pair is a `Span { lo, hi }` and every `origin: String` a `FileId` into one `SourceMap` per load; `Error` resolves at `in_file`/`placed`. Both snapshots unchanged, a 7 342-line diagnostic corpus byte-identical, erc20_full LSP diagnostics 6.28–6.87 → 6.23–6.26 ms (not moved beyond noise). See `## 5.2a`.
- [x] **5.3** Remove deep clones. Make `Plan` cheap. **Measured, not taken:** a Release `Plan` clone with 640 set members costs **3.0 µs**; `bench/erc20_full.lithe` Release runs 98 emits and 92 finishes totalling 1.66 s. The ~200 plan clones a search does are therefore ~0.6 ms, 0.04 % of the backend. The clones that matter are `Program`'s, and 5.1/5.2 removed them. See `## 5.3 Plan clones measured`.
- [x] **5.4** Fx hasher. Every std `HashMap`/`HashSet` in `check`, `gen`, `route`, `split` and `index` (and `asm.rs`'s last few) is now `asm::FxHashMap`/`FxHashSet`; the two whose order was seen are `BTreeMap`s (no `IndexMap`: no new dependency). Both snapshots unchanged; `check` −1.5–2 %. See `## S27 Fx hashing`.
- [x] **5.5** Index-arena AST. **Measured and not taken (S32):** the flip is 1 378 errors in 41 files, and its payoff is 0.08 % of a Release build and 1.2–1.7 % of a Fast one — 3 `Program` clones per build (0.4–0.9 ms in total: 0.6–0.9 ms Fast, 0.4 ms Release), which a flat `Vec<Expr>` does not make cheaper (159 µs vs 142 µs on erc20_full, because the cost is `Program.modules`, not the expression tree). `Checked.source` cannot be removed by borrowing: it is the program *before* `compose` inlines modules, so it is a different value, not the same value held twice. See `## S32 5.5 closed: not taken`.
- [x] **5.6** Parsed and checked module cache across `compile_dir` and `abi_dir`. **Parsed half landed; checked half is already shared per file.** `emit_dir` now holds one `ModuleCache` for the directory, so the `lib/` files 51 bench entries import are parsed once instead of once per importer (68 parses → 68, 43 of them hits). Byte-identical output and thread-count-independent. The directory build is 360 ms at one thread of which **loading is 20 ms and parsing 3.6 ms**; the 300 ms is codegen, which is why the number does not move beyond noise. The checked half has nothing to add: `check` runs per entry file on its own merged program, and two entries' programs are different types, so no entry reuses another's `Checked` — that memo already serves the LSP, where the same file checks twice. See `## 5.6`.
- [x] **5.7** Lexer slices and statement-level parser recovery. First error unchanged. **Landed (S30):** the lexer already kept no identifier payload (a `Token` is a byte range and the parser slices it), so the slices half needed one fix: `ident()` interned the text and returned a `String` that every `Expr`/`TypeRef`/`NameAt` site then interned *again* through `sym()`. `ident()` now has an `ident_sym()` form that interns once, and the expression, type, dotted-name and call sites use it — **34 940 → 23 833** intern calls on erc20_full, **24 293 → 14 986** on uniswap_v2_pair, **24 276 → 15 220** on erc1155 (down 32–38 %). Declaration fields that hold a `String` still take the text. Statement-level recovery is new: a broken statement in a block reports its error, the parser skips to the next `;` or `}` and parses on, so a file reports every broken statement in file order with the first one unchanged. Both bytecode snapshots, the differential gate at 2 000 steps, and a 27 892-line diagnostic corpus over `bench/`+`examples/`+`fuzz/`+`std/` in both modes are byte-identical to the parent. The LSP diagnostics number did not move (6.91 vs 6.97 ms). **S59** then made `skip_stmt` bracket-kind aware (S30's open finding): an unclosed `(`/`[` no longer eats the block's `}` and takes recovery past the declaration, so a second broken function reports its own error instead of a spurious end-of-file one. See `## S30 5.7` and `## S59 5.7 skip_stmt brackets`.

### Phase 6 — evaluate and take if they pay

- [x] **6.1** Process startup. Measured; not taken.
- [x] **6.2** Assembler width fixpoint. It already is one, and candidate cost is already cached. Nothing taken.
- [x] **6.3** Memoize constant keccak. Measured; not taken.
- [x] **6.4** Incremental `heat` / `flow`. Taken in 3.2b(ii) as a skeleton-keyed `flow` cache with a ~5% hit rate; goal missed, and 3.2c reached the same goal the other way (fewer `merge_tails` calls, so `heat` runs on 1019 calls instead of 1940 on erc20_full) rather than by making one call cheaper.
- [x] **6.5** `--timings`, and CI that fails when erc20_full Fast compile exceeds 2× the recorded baseline. Landed (S41): the flag is the `LITHE_TIME` line, and the `perf` job gates 7 runs at 118 ms. See `## S41 6.5 --timings and the perf gate`.

## State

This section is the single source of truth for what is open and what blocks what. Older sections below are dated records; where they disagree, this one wins.

- **2.5 landed** (`ad6adc5`): LSP diagnostics on `bench/erc20_full.lithe` about 12 ms at the unrelaxed 20 ms limit.
- **2.6 in this branch:** the index is lazy and diagnostics take 6.3–6.5 ms (release, quiet) and 7.7–7.9 ms (dev). The ≤ 5 ms target is missed because `check` alone is 5.1–7.0 ms and is the floor. Reaching it is Phase 5 frontend work (interner, spans, `Program` clones), not more LSP work; `## 2.6` has the split and owns the number.
- **3.2b/3.2b(ii) landed** (`f34c8a8`), goal missed under byte-identity.
- **3.2c in this branch:** `merge_tails` merges every free pair per call; gated and recorded in `## 3.2c`. erc20_full Release `optimize` 382.0 → 301.3 ms, ladder 128 Fast 251.1 → 31.0 ms (min of 7 alternating runs, load 2.0). Against the **pre-3.1** cost re-measured at load 1.6–2.1, erc20_full is 340.4 → 306.3 ms (goal met) and uniswap_v2_pair is 57.8 → 62.4 ms (**still 4 % over**, from the two extra candidate builds 3.3b(ii)'s `Move::Batch` adds, not from the pass). The per-span `peephole` overhead was not touched.
- **3.4b landed** (`fc4921d`), final bytes unchanged; re-verified at `3a670f0` after 3.2b/3.2c rewrote `flow_` and `merge_tails` (exact pass 0–4 rounds, 53 targets byte-identical in both modes). Incremental `flow` between rounds measured at 10–12% of the `outline_once` loop — a few tens of ms of a multi-second build; not taken (see 3.4b re-verified).
- **3.3b(ii) landed.** Batched promotion (below). Rounds are 4 at ladder N = 16/64/128 (were 34/130/258) and ladder 128 Fast `promote` 49.6 → 12.0 ms. It is `Plan::batch`, default on in the start plan, tried off by the search as `Move::Batch`. Sizes: runtime bytes −0.027 % over the 272 target-modes (parent → here), and −0.153 % creation + runtime over the 13 whose code changes; the `Fast` increases behind that (`nft` +74, `utils` +14, `governance_token` +2, `erc20_full` +2) are the batched start plan's own price, since `Fast` builds that plan and nothing else and has no candidate to decline it. Gas: **transaction gas +0.0002 %** (the step totals, 68 121 512 → 68 121 662) and **gas including deploy −0.018 %** (96 454 261 → 96 437 353); every step outcome identical. See `## 3.3b(ii)` for the tables.
- **3.3c measured, not taken (S40, reproduced by S53).** `LITHE_PRICE_BATCH=1` prices every plan the Release search builds with `batch` on and off. Over the 51 `bench/*.lithe`: 1 140 pairs, 103 wins, 1 015 ties, **22 losses** (erc20_full 12, erc721_full 4, erc721 3, fixed_point, uniswap_v2_factory, uniswap_v2_pair 1 each; worst +0.96 % cost on erc721). The deletion's own condition fails, so the greedy `promote_region` path, `Plan::batch` and `Move::Batch` stay. The command and the comparison with S40's scratch count are in `## S40 3.3c priced`.
- **3.3 closed as not taken (S48).** The value-numbering scheduler is not built. `promote` is 8.9 % of the Fast backend over `bench/` and 3–4 % on the ladder, so the rewrite moves no open target. The record also covers what 3.3 owed beyond compile time. Size and gas are within budget: runtime −0.027 % and deploy-inclusive gas −0.018 %, but transaction gas is +0.0002 %, so §5's expected gas improvement is not delivered. The stack-too-deep guarantee comes from memory homes plus the `< 16` reach checks in `hold`/`plan_region`/`walk_alias`/`abandon_walk` and the outliner, with no spilling. See `## S48 3.3 closed: not taken`.
- **4.1 closed as not taken (S23).** Per-body emission, the only per-function unit before `resolve`, is 9.1 % of the Fast backend and 8.2 % of Release (50 `bench/` files, `LITHE_THREADS=1`). The `[time]` line now reports it as `body`. Unlimited threads would give at most 1.10×, and the join would have to rebuild each body's shared emitter state. `parallel_map` still parallelises plan candidates only. Release output is byte-identical at 1 and 16 threads over all 51 `bench/` files and ladder 128. The command and digests for erc20_full, ladder 128 and factory, in both modes, are recorded there (S55). See `## S23 4.1 closed: not taken`.
- **4.2 landed (S24).** Sibling units build on the pool, in declaration order. They are byte-identical at 1 and 16 threads, and no benchmark moves because only `examples/factory.lithe` has two units. See `## S24 4.2`.
- **3.5 met, closed (S50).** The ≤ 1.5× per-line bar from 439 to 1735 lines is met on this tree with no new code: **Fast 0.63×, Release 0.90×** (min of 5 runs; medians 0.59× / 0.87×). The step that closed it was already-landed 3.2c (`merge_tails` takes its next-best free pair) plus 3.3b(ii) (batched promotion); the 3.5 table was written before both. What remains is a much weaker superlinear term that starts past the measured range (Release 1735→3463 is 1.30×, 3463→6919 1.81×). Measurement, method and the residual in `## S50 3.5 closed`.
- **Final comparison table regenerated (S43).** `## Comparison with baseline.json` is now the finished branch at `6646998`, not the mid-branch snapshot: every `bench/` contract and the ladder, Release and Fast, `LITHE_THREADS=1` and 16, gas and step outcomes against `baseline.json`. Whole set at one thread: 20 409 → 13 148 ms Release (**1.55×**), 6 360 ms Release at 16 threads, 1 995 ms Fast (**10.2×**). `erc20_full` Fast 1 731.9 → 50.4 ms. Transaction gas +0.0022 % Release, deploy-inclusive +0.042 %; bytes +0.08 % without the ladder. 3.5's bar re-measures at **0.64× Fast / 0.92× Release** on this tree, consistent with S50's 0.63× / 0.90×. The architecture page was checked line by line against the tree; two sentences were wrong and are corrected (a `JUMPI` does not end a block, and `promote` is priced by bytes, not by `asm::gas`) — see the section's closing note.

- **5.1 measured, handoff: needs its own slice.** The interner was started and the exact cost measured before writing it. Details and the number that decides the split are in `## 5.1 Interning: scope measured`.
- **5.1c landed (S29):** `Checker.named`/`domain_tys`, `Scope.vars` and `Checked.named`/`domain_tys` are `FxHashMap<Symbol, _>`; `route::InternalNames` and `index`'s type-name table sort on `Names::get` text so ABI `internalType` and hover names keep their parent order; `type_name` picks the alphabetically smallest of a type's names where the parent picked a hash-order one (deterministic now, no corpus diagnostic moved). `check` on erc20_full 5.83 → 5.67 ms (min of 25, interleaved A/B); both snapshots and a 52 213-line, 1 225-invocation diagnostic corpus byte-identical. See `## 5.1c`.
- **5.2a landed (S57):** byte spans and `FileId`s across the crate, positions resolved from a per-load `SourceMap`; bytecode, diagnostics, warnings, lint and prover text unchanged. The LSP number did not move (6.2 ms), so the ≤ 5 ms target still rests on 5.1b/5.1c and 5.5. See `## 5.2a`.
- **5.5 closed as not taken (S32).** No arena; the AST keeps boxed expressions. Measured before writing it: the flip is **1 378 errors in 41 files** (a whole-crate sweep, not a frontend-hygiene slice), and the two `Program` clones it was to remove are **3 clones per build, 0.4–0.9 ms in total — 0.08 % of a Release build and 1.2–1.7 % of a Fast one**. A flat `Vec<Expr>` cloned on its own is *slower* than the tree on erc20_full (159 µs vs 142 µs), because the cost is `Program.modules`, not the expression tree. And `Checked.source` is not removable by borrowing: it is the program *before* `compose` inlines modules and qualifies their names, so it is a different value from `checked.prog`, not the same one held twice — three readers (`split::facet`, `split::cache_key`, `index::template`) depend on exactly that. See `## S32 5.5 closed: not taken`.
- **5.1a landed:** `Symbol`/`Names` and `Program.names`, one process-wide table threaded through `parse`, `parse_specs` and `load_in`, with a determinism test across files and parse orders. No field moved, so bytecode and diagnostics are unchanged. See `## 5.1a The table`.
- **5.7 landed (S30):** the parser interns each identifier once (every expression, type, dotted-name and call site went through `ident()`'s `String` and `sym()`'s second intern) and recovers from a broken statement so a file reports all of them, the first unchanged. Interning calls fall 32–38 % per file; the LSP number does not move (6.91 vs 6.97 ms), because `parse` is 0.14 ms of a 6.2 ms frontend. Bytecode, diagnostics, snapshots and the differential gate unchanged. See `## S30 5.7`.
- **S59 landed: 5.7 recovery is bracket-kind aware.** `skip_stmt` counted `{`, `[` and `(` in one depth, so an unclosed `(`/`[` above a statement made the block's own `}` look like a closer: it was consumed, recovery carried past the end of the declaration and the file reported a spurious ``expected `}`, found end of file`` in place of the next function's real error. It now tracks the three kinds separately, so a `}` with only parens/brackets open ends the statement *without* consuming it, and a closer with nothing of its kind open saturates at zero instead of underflowing. Two `parse::tests` regressions cover it; the diagnostic corpus (`abi`/`compile`/`specs`/`lint` + `errors`, 41 610 + 13 295 lines, plus S30's `abi`/`compile --release` shape at 38 123) is byte-identical to the parent, both snapshots unchanged, `make check` green. See `## S59 5.7 skip_stmt brackets`.
- **5.1b landed (S58):** `NameAt.name`, `Expr::{Ident, Field, Call}` and `TypeRef::Name` hold a `Symbol`; every diagnostic reads its text through the table, `Symbol`'s `Debug`/`Display` print the text (never the number) so `Program`'s `Debug` cache keys are unchanged, and `modules::imply`'s order-by-name sorts on text. Both snapshots unchanged, both suites and VERIFY green, the differential gate green at 2 000 steps, and 36 369 lines of diagnostics byte-identical to `411bf45`. Two reviewer findings then fixed it: a call's module qualification read a name captured before the alias rename (a module calling `A.f` while declaring its own hook `f` ran its own hook), and `zero_value`'s `None` lost its name; both now have failing-first regression tests. `check` on erc20_full is 5.05 → 5.90 ms (min of 25, cache off): the lookup replaces an inline `String` 138 263 times per compile, which is 5.1c's number to invert. See `## 5.1b`.
- **S43 and S44 landed:** one process-wide `LITHE_THREADS` budget, and per-build timing counters. See `## S43 One thread budget` and `## S44 Per-build counters`.
- **S37/S45 landed:** build state no longer depends on how much of the thread budget was free. `parallel_map` releases a worker's unit as soon as the queue drains, workers start from the caller's byte weight, certifying and tracking, and the `LITHE_TIME` counters are thread-local, summed back by the pool. A parallel `compile_dir` now prints one `[time]` line per build, each with its own `emits`/`finishes`. See `## S37/S45 build state off the budget`.
- **S49 landed:** the `simplify:` list in `src/evm/bench_gas.rs` now matches `Meter`/`charge()` — the seed is EIP-2929's precompile set 1..=0x11, and the two addresses it leaves cold until first touched (`0x100` P256VERIFY, and anything `CREATE`/`CREATE2` made) are named. Doc-only; no gas total moved. See `## S49`.
- **S51 landed, `make check` green.** S37's three open findings: `split::facet` no longer answers from its process-wide memo while a test forces a codegen knob (`gen::forced()`), `parallel_map` merges a pool's certificates in item order so a proof is the same at any `LITHE_THREADS`, and worker `Track` notes are deliberately not merged (their labels belong to one build) with the caller's track returned untouched. The whole-suite `LITHE_VERIFY` failure this tree carried since `b8fc4fa` is gone: 558 lib tests pass under VERIFY, 0 fail. See `## S51 S37's findings, and make check green`.
- **S52 landed:** S51's three residual findings. A pool keeps the caller's pre-pool certificates ahead of its items', a worker sees the caller's forced codegen knobs, and the item-order test compares the pool at one thread with the pool at N. See `## S52 S51's residual findings`.
- **S27 landed (5.4):** Fx hashing in `check`/`gen`/`route`/`split`/`index`; `BTreeMap` where order is seen. See `## S27 Fx hashing`.
- **S40 measured, not taken:** see the 3.3c bullet above.
- **S53 landed:** the S40 instrument is `LITHE_PRICE_BATCH`. With it set, all 51 `--release` outputs are byte-identical, and both snapshots are unchanged.
- **S41 landed (6.5):** `--timings` sets `LITHE_TIME=1` before any command runs, so it prints the `[time]` line the harness already parses; a `perf` CI job fails when the best of seven Fast compiles of `bench/erc20_full.lithe` at one thread exceeds 118 ms (2× the 59 ms baseline in `## 1.1`), and is in `success`'s `needs`. See `## S41 6.5 --timings and the perf gate`.

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
- **The 500-round bound.** It is still there as a guard against passes that never settle. Its output is identical as long as the bound is never reached. Rounds on ladder 128 stay at about 131 per `optimize`, because `merge_tails` applies about one merge per group per call: a block that loses to a longer pair poisons its partner. Fewer rounds means merging more per call, which changes codegen. That belongs to 3.2b.
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

## 2.6 The index on demand, and the missed 5 ms target

Plan: take `index::build` off the diagnostics path, since no diagnostic needs an index. Time the test in both profiles and set its limits from the measurement. Expect ~12 → ~6.5 ms and still miss ≤ 5 ms.

What changed: `ModuleCache::analyze_edit` runs the frontend without building the index and says whether `ModuleCache::index` would return one. `Doc` keeps `unindexed: Option<String>`, the text whose index is not built yet, and `index_now` builds it from that text the first time a request needs it (hover, definition, references, highlight, symbols, completion, signature help, rename, workspace symbol). No answer changes: the index is built from the same checked units, just later. Diagnostics are published before the index exists, so a keystroke costs load, check, and lint.

`LITHE_TIME=1 cargo test --release --bin lithe did_change_coalesces -- --nocapture`, quiet machine (load 0.07), best of five per run, three runs: the frontend laps are load 0.73–2.4 ms, `check` 5.1–7.0 ms, `lint` 0.35–0.55 ms, `index` 60–140 ns (the lap is now the `unindexed` clone). The timed publish is **6.3 / 6.4 / 6.5 ms**.

`cargo test --bin lithe` (dev, `opt-level = 2`): 7.7 / 7.7 / 7.9 ms. Under 32 spinning processes on 16 cores it is 20.8–41.9 ms, so the dev allowance is 60 ms as 2.3 recorded it; the optimized limit is the unrelaxed 20 ms. `620.0` was a mis-scaled dev number that made the assertion unreachable in release (`limit 0.0`), and both are now the measured pair.

**The ≤ 5 ms target is missed.** `check` alone is 5.1–7.0 ms and is the floor: no further LSP work moves it, because the server has nothing left to skip. Getting under 5 ms means making the frontend cheaper — the interner (5.1), spans (5.2), and the `Program` clones (5.3) — so this is Phase 5 work, and the number to re-measure is this test's, unchanged, at the 20 ms limit it already has.

Tests: `cargo test --locked` (553 lib + 25 bin + 1, green), `cargo test --release --bin lithe` (25 green, including this test at the 20 ms limit), `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check`.

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

**Floor: about 376 ms / 66 ms, measured at machine load 19–47; the 339 / 59.9 ms goals were not measured under that load, so the two are not yet comparable (3.2c re-measures both under recorded low load). The goal is missed.** `flow`'s cost is per block, not per instruction, and no single phase holds the 37 ms gap. Split of `flow` over one erc20_full compile (temporary timers): starts 8, label map 11, successors 11, cold fixpoint 6.5, DFS 9, preds 5, indeg 3, entry walk 23 ms. Heat is called once per merge round. Getting under 339 ms needs fewer `merge_tails` calls, by merging more per call (3.4, which changes bytes), or the per-span `peephole` overrun (≈95 ms) recovered. Neither fits under the byte-identity constraint here.

Resolved in 3.2c: fewer `merge_tails` calls per compile was taken (next-best free pair per call), and the pre-3.1 comparison was re-run at recorded low load. erc20_full Release is 306.3 ms against the 339 ms goal; uniswap_v2_pair is 62.4 ms against 59.9 ms, and the 2 extra candidate builds 3.3b(ii) adds are what hold it over. See `## 3.2c`.

Gates at this head:
- `cargo test --locked` (dev profile): 552 lib + 25 bin + 1, green.
- `LITHE_VERIFY=1 cargo test --locked`: 552 lib + 25 bin + 1, green.
- `tests/snapshots/bytecode.json` unchanged (Release and Fast, plus under verify). `rounds_on_blocks_match_the_stream` and `incremental_analyses_agree_with_fresh_ones` green.
- `LITHE_FUZZ_STEPS=2000` differential: 5 tests green.
- Playground `cargo build --release --locked` (wasm32-unknown-unknown): builds.
- `cargo fmt --check` clean in the root and in `playground`. `cargo clippy --all-targets --locked -- -D warnings` clean.

The 2.5 `LITHE_TIME` frontend lap now reports codegen as its own `build=` phase. On the uncached path `check=` used to include it. On the cached path it was not timed at all. Repeated marks of the same phase add up.

## 3.2c `merge_tails` takes its next-best free pair

**Plan.** `merge_tails` applied at most one merge per block per call, and a block whose best partner was already taken in that call counted as used anyway: it was out for the rest of the call and waited for the next one. Every call costs a whole `stream_heat`, so a lost pairing cost a round. The hunk is 11 lines in `Blocks::merge_tails`: skip a pair without marking either block, so a block whose partner is gone can still take a smaller pair in the same call.

```rust
for &(a, b, n, _) in &pairs {
    if used[a] || used[b] {
        continue;
    }
    used[a] = true;
    used[b] = true;
```

That changes which pairs get merged, so it moves bytes, and this step is the gate and the record rather than the implementation. The counterfactual below restores the old gate (`let free = …; used[a] = true; used[b] = true; if !free { continue; }`) and nothing else; both binaries are `[profile.fast]` builds of the same commit, so the difference is the hunk.

`optimize` sum and its neighbours, min of 7 alternating runs, `LITHE_THREADS=1`, cache off, one-minute load 2.0 at both ends of the run:

| target | mode | optimize before → after | backend | promote | outline+ | emits / finishes |
|---|---|---:|---:|---:|---:|---|
| `bench/erc20_full.lithe` | release | 382.0 → **301.3 ms** | 1676.0 → 1557.5 | 544.2 → 541.5 | 458.8 → 426.3 | 99/99, 93/93 |
| `bench/uniswap_v2_pair.lithe` | release | 67.4 → **63.0 ms** | 362.8 → 357.1 | 120.8 → 120.1 | 97.0 → 96.7 | 37/37, 34/34 |
| `bench/erc1155.lithe` | release | 141.0 → **121.8 ms** | 607.9 → 593.7 | 159.4 → 158.7 | 204.0 → 206.3 | 61/61, 51/51 |
| `bench/erc20_full.lithe` | fast | 13.3 → **12.6 ms** | 41.3 → 40.3 | 5.1 → 5.1 | 10.1 → 9.9 | 1/1, 2/2 |
| `scaling/n64` | fast | 56.2 → **15.3 ms** | 84.9 → 43.5 | 1.9 → 1.9 | 9.3 → 9.2 | 1/1, 2/2 |
| `scaling/n128` | fast | 251.1 → **31.0 ms** | 338.1 → 117.7 | 4.5 → 4.5 | 21.7 → 21.5 | 1/1, 2/2 |

`promote` is the same work in both binaries — it runs before `optimize` and its input is identical — so the 0.1–0.7 ms spread in its column is timer noise, and its emit/finish counts are equal on every row.

**Pass split** (temporary timers around each pass inside `blocks::optimize`, since removed; min of 7 alternating runs at load 2.08, milliseconds). These counters are process-wide and cover every `blocks::optimize` — including the ones `outline` runs — so the sum exceeds the `optimize` timer above:

| target | | prune | thread | peephole | dedup | dup_const | merge_tails | schedule | rounds | `merge_tails` calls |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| erc20_full R | before | 39.4 | 23.7 | 95.0 | 66.1 | 75.5 | **161.8** | 74.5 | 2692 | 1940 |
| | after | 35.1 | 21.3 | 81.3 | 60.1 | 63.0 | **96.3** | 74.2 | 2362 | 1019 |
| uniswap_v2_pair R | before | 6.1 | 3.5 | 14.8 | 10.5 | 11.8 | 20.8 | 22.4 | 511 | 381 |
| | after | 6.0 | 3.5 | 14.5 | 10.8 | 11.3 | 15.6 | 22.8 | 511 | 245 |
| erc1155 R | before | 14.0 | 7.9 | 35.4 | 32.2 | 26.3 | 36.3 | 28.1 | 1184 | 713 |
| | after | 12.9 | 7.4 | 31.8 | 29.4 | 23.4 | 27.0 | 28.6 | 1066 | 437 |
| ladder 64 F | before | 3.6 | 2.0 | 9.7 | 7.2 | 4.8 | 25.1 | 5.3 | 143 | 135 |
| | after | 1.2 | 0.7 | 2.9 | 2.3 | 1.4 | 3.0 | 5.1 | 49 | 21 |
| ladder 128 F | before | 14.1 | 7.8 | 37.5 | 28.6 | 18.5 | **140.0** | 7.0 | 271 | 263 |
| | after | 2.6 | 1.6 | 6.6 | 5.3 | 3.1 | **7.8** | 6.3 | 55 | 23 |

Two effects, and only the first is `merge_tails`'s own cost.

**Fewer calls.** 1940 → 1019 on erc20_full, 263 → 23 on ladder 128. On erc20_full a call now costs more, 0.083 → 0.095 ms (+13 %: more pair comparisons, and one `stream_heat` covering several merges instead of one), and on ladder 128 it costs less, 0.53 → 0.34 ms, because the early calls no longer leave most exits unpaired. Either way the totals fall: 1.7× on the real contracts (161.8 → 96.3 ms) and 18× on the ladder (140.0 → 7.8 ms).

**Fewer rounds.** 2692 → 2362 on erc20_full, 271 → 55 on ladder 128, because a call that merges every free pair reaches the pass's fixed point in fewer rounds. That is what shrinks every other pass: `peephole` 37.5 → 6.6 ms on ladder 128 is the same `peephole` run in 55 rounds instead of 271. `schedule` is unchanged because it only runs in a round where the earlier passes found nothing, and once `merge_tails` has a stream it changes nothing more. Rounds exceed `merge_tails` calls because `merge_tails` is skipped in any round the earlier passes did change something.

**The pre-3.1 floor, which 3.2b(ii) recorded as owed.** 3.2b(ii) measured 376 ms / 66 ms at load 19–47 against goals of 339 ms / 59.9 ms set before 3.1, and wrote that the two were not yet comparable (3.2c re-measures both under recorded low load). Done, min of 7 alternating runs, load 1.59 and 2.14:

| target | mode | 3.0 (`b9b5acd`, before 3.1) | this tree | pre-3.1 goal |
|---|---|---:|---:|---:|
| `bench/erc20_full.lithe` | release | 340.4 ms (97 emits / 91 finishes) | **306.3 ms** (99 / 93) | 339 ms — **met** |
| `bench/uniswap_v2_pair.lithe` | release | 57.8 ms (35 / 33) | 62.4 ms (37 / 34) | 59.9 ms — **missed by 4 %** |

So the erc20_full gap 3.2b(ii) could not close is closed: `optimize` is 10 % below its pre-3.1 cost. `uniswap_v2_pair` is not, and the reason is the search's size, not the pass: this tree runs two more emits and one more finish than 3.0, which is the `Move::Batch` candidate 3.3b(ii) added for the search to price (S40 measures whether that dimension earns its place and removes it if it does not). Per finish the pair's `optimize` is 1.75 → 1.84 ms (+4.8 %), and the total is +8.0 % over two extra candidate builds. Recorded as missed rather than softened: 3.2c's own hunk makes the pass cheaper on this target too, it just does not pay back the extra finish 3.3b(ii) added.

These two tables give the same binary two values for the pair: 62.4 ms here and 63.0 ms in the table above, 1 % apart, from separate 7-run sets. Both are min-of-7 at load under 2.2; the pair has the smallest `optimize` of the five targets and therefore the widest relative noise.

**Size, over every target.** 152 files, both modes (304 target-modes): all of `bench/`, the `examples/` and `fuzz/` trees `differential_targets` accepts, and the ladders at N = 64 and 128. Creation and runtime bytes from `lithe compile`, counterfactual vs this tree:

| measure | before | after | delta |
|---|---:|---:|---:|
| runtime bytes, all 304 target-modes | 464 161 | 464 497 | **+0.072 %** |
| creation bytes, all 304 target-modes | 500 510 | 500 784 | +0.055 % |
| runtime bytes, Release only (152) | 231 178 | 231 498 | +0.138 % |
| runtime bytes, Fast only (152) | 232 983 | 232 999 | +0.007 % |
| runtime bytes, `bench/` only (102) | 177 990 | 178 075 | +0.048 % |
| creation + runtime, the 34 changed target-modes | 281 557 | 282 167 | +0.217 % |

34 of the 304 target-modes change at all; the rest are byte-identical, including every ladder row in both modes. The worst per target is `erc6909`/`claims` Release runtime 3326 → 3423 (+2.92 %), then `stdlib/token` Release 2520 → 2566 (+1.83 %), `ownable_roles` Release 1042 → 1056 (+1.34 %) and `erc20` Release 2244 → 2269 (+1.11 %). Six move down: `erc4626` Release 2884 → 2821 (−2.18 %) and Fast 3120 → 3063 (−1.83 %), `erc721_full` Release 5640 → 5624 (−0.28 %), and three by a byte or two (`fuzz/arith` both modes, `uniswap_v2/factory` Fast).

Two notes so the numbers are not read as more than they are. **The §2 gate is on totals, and the totals pass**: +0.072 % runtime against a 1 % allowance. Five target-modes are over 1 % on their own, four distinct programs: `erc6909` and `examples/stdlib/claims` (the same contract under two names, +97 bytes each on 3326), `stdlib/token` +46 on 2520, `ownable_roles` +14 on 1042, `erc20` +25 on 2244. They are the cost of a batched merge reaching a different pair set, not a leak: the pair `merge_tails` now takes instead of waiting is chosen by the same `saved ≥ 0` test against the same heat model, so a local loss with a global gain is what the pass is allowed to produce. Nothing on a revert or check path changes, and every suite's outcomes are identical. **The 34 changed target-modes and the snapshot's 34 changed keys are the same set** — checked key by key, `path:Contract` in Release and `path:Contract:fast` in Fast.

**Gas, `evm::bench_gas`, all 45 suites, on the identical binaries the snapshot hashes.** Every step's ok/revert status and every suite's status vector are unchanged. The one suite whose returndata hashes move is `uniswap_v2` (12 of 139 steps), and for the reason already recorded in 1.2: the factory creates its pair with CREATE2, the factory's own runtime grew a byte (6038 → 6039), so the pair address and the `DOMAIN_SEPARATOR` that commits to it differ — steps 12, 13, 16–18, 21, 30, 126–129 and 131, exactly the ones that read a CREATE2-derived address. Status stays `ok` throughout.

| measure | before | after | delta |
|---|---:|---:|---:|
| transaction gas, 45 suites | 68 120 851 | 68 121 662 | **+0.0012 %** |
| deploy gas, 45 suites | 28 259 326 | 28 315 691 | +0.1995 % |
| gas including deploy | 96 380 177 | 96 437 353 | +0.0593 % |
| suite runtime bytes | 105 796 | 106 059 | +0.2486 % |

11 of the 45 suites move at all: `codec`, `erc20`, `erc721`, `erc1155`, `erc6909`, `erc721_full`, `erc4626`, `safe_erc20`, `erc20_full`, `uniswap_v2`, `staking`. `erc4626` is the only one that moves down once deploy is counted (transaction gas +1 049, deploy −8 250, bytes 5256 → 5218, net −7 201); the rest are small increases, the largest being `erc6909`'s 97 bytes of runtime.

**Snapshot.** `tests/snapshots/bytecode.json` was regenerated for this change at `26cc9d1`: 34 of its 290 keys change — 19 Release and 15 Fast, the 34 targets in the size table above, checked key by key against it. Four are Release-only (`erc20`, `erc20_full`, `stdlib/token`, `stdlib/ownable_roles`) because Fast builds a different plan there. At this head the file differs from the pre-3.2c tree by 43 keys: 3.2c's 34, plus the 13 that 3.3b(ii) moved afterwards, 4 of which 3.2c had already moved. No key is counted twice and `evm::snapshot` passes in both modes and under `LITHE_VERIFY`.

**Gates at this head** (`ab6c382`, the merged branch, nothing uncommitted):
- `cargo test --locked --offline`: 553 lib + 25 bin + 1 doctest, 0 failed.
- `LITHE_VERIFY=1 cargo test --locked --offline --lib`: 553 passed, 2 ignored — the `region_batch` and incremental-against-fresh oracles run on every round.
- `LITHE_FUZZ_STEPS=5000 cargo test --lib evm::differential`: 5 passed.
- `cargo test --lib evm::prove`: 38 passed, 2 ignored, including the three bytecode-level proofs.
- `cargo test --lib evm::snapshot`: both tests, including the `LITHE_VERIFY` one.
- `LITHE_BENCH_OUT=… cargo test --lib evm::bench_gas::bench_gas -- --exact`: green, 45 suites.
- `cargo clippy --all-targets -- -D warnings` and `cargo fmt --check` clean, root and `playground`.
- Playground `cargo build --release --locked` (wasm32-unknown-unknown) builds.
- Determinism: ladder 128 Release byte-identical at `LITHE_THREADS` 1/4/16; `erc20_full` Release byte-identical at 1/8.

**One machine note for the next reader.** Several timing sets were discarded for load: the box went from 1.6 to 43 within one set. Every number above was taken with the one-minute load average below 3 at the start and at the end of the run it is in, and the load is stated where it is not. What load does to these figures, measured on the same `bin-after` binary: `optimize` on erc20_full is 306.3 ms at load 2.1 and 761.0 ms at load 43 — 2.5×, with `promote` and `backend` inflated by the same factor. At load 18 the same binary's counterfactual pair reads 385.9 / 299.2 against 382.0 / 301.3 at load 2.0, which is inside noise. So `LITHE_THREADS=1` does not make a timing immune to load: the process still competes for cores, and only a measurement that states its load is worth reading.

The pair this step previously carried — 346 → 271 ms on erc20_full, 237 → 29 ms on ladder 128 — records no load and no counterfactual binary, so it cannot be reproduced, and it was measured at `26cc9d1`, before 3.3b(ii) added `Move::Batch` to every Release round. The reduction it reports (−21.7 % / −87.8 %) is the same one measured above (−21.1 % / −87.7 %); the absolute values differ because the earlier "before" is not the same program. What this section adds beyond the ratio is the load, the counterfactual, the pass split, the pre-3.1 comparison, and the size and gas the step was owed.

## 5.3 Plan clones measured

The step lists four clones. Three are `Program` clones whose removal needs the interner and spans (5.1/5.2) to be worth doing; one, `Plan::clone` per candidate, was measured on its own.

`Plan` is 78 fields: a dozen `HashSet`s plus a handful of `HashSet<String>` (`shared_raises`) and `HashSet<(usize, usize)>` (`split_insts`). A clone with 640 members across all of them, timed in a test over 200 iterations at `--profile fast`:

```
plan clone: 3.026µs
```

`bench/erc20_full.lithe`, `--release`, `LITHE_THREADS=1`, `target/fast`:

```
[time] check=5.483297ms backend=1.658849764s | emits=98 sum=821.768905ms (promote 641.866392ms, 13242 rounds) | finishes=92 sum=787.256755ms (optimize 293.418076ms, outline+ 429.479854ms)
```

A search of 98 emits does on the order of 200 `Plan` clones: 200 × 3 µs ≈ **0.6 ms of 1659 ms, or 0.04 %**. Making `Plan` a bitset plus `Arc` sets would buy that, at the cost of changing every one of its ~78 fields to a different type and every `.insert`/`.remove`/`.contains` on them — a large diff for a number inside the run-to-run noise of the measurement above.

**Not taken, and recorded as such per the loop rules.** If a later slice makes the search cheaper this gets proportionally *less* worth doing, not more, so it should not be revisited unless the emit count rises by an order of magnitude. The `Program` clones the step also lists are removed by 5.1/5.2 (`Checked.source`, `analyze`'s `unit.clone()`, `spec::check(prog.clone())`) because those steps change what `Program` holds; removing them first would be the same wide diff without the interner's payoff.

## S43 One thread budget

**Plan.** `LITHE_THREADS=N` was applied per pool: `gen::parallel_map` capped itself at N, `split::parallel` capped itself at N again, and `lib.rs::emit_dir` ignored the variable and used `available_parallelism`. N facets each searching N plans therefore ran N² threads. Replace all three with one process-wide permit counter; bytecode must not change.

**What changed.**
- `gen::budget()` — the process's thread count: `LITHE_THREADS`, else one per core. One `OnceLock`, so every caller agrees.
- `gen::claim()` — takes a unit of the remaining budget; the `Unit` guard returns it on drop. The pool's own thread counts as the first thread, so `SPARE` starts at `budget - 1`.
- `gen::parallel_map` — spawns while it can claim a unit and work remains; the calling thread then runs `work()` too. With no unit free every item runs inline, in order.
- `split::parallel` — now just `gen::parallel_map(..).into_iter().collect()`. The two pools were already the same shape, so the duplicate 64 MB-thread spawner is gone.
- `lib.rs::emit_dir` — worker count from `gen::budget()`, and its extra threads claim from the same counter.

**Why it cannot regress bytecode.** Pool results were already collected by index and sorted before use (`done.sort_by_key(|(i, _)| *i)`), so join order never reached the output. The change decides only *where* an item runs, never what it computes.

**Proof.** `gen::shared_budget_bounds_nested_pools` runs 8 outer items each pooling 4 inner ones — the facet-times-candidate shape — and asserts peak concurrent inner tasks never exceed `budget()`. Green at `LITHE_THREADS` = 1, 2, 3, 8, 64, and with the variable unset.

`target/fast/lithe compile --release`, cache off, SHA-256 of the emitted code, 1 thread vs 8, load average 24–58 on 16 cores:

| contract | `LITHE_THREADS=1` | `LITHE_THREADS=8` |
|---|---|---|
| `bench/erc20_full.lithe` | `c9e95d55a93c` | `c9e95d55a93c` |
| `bench/uniswap_v2_pair.lithe` | `3a64c353a3f7` | `3a64c353a3f7` |
| `bench/erc1155.lithe` | `1d9afd031948` | `1d9afd031948` |
| `bench/solady_erc20.lithe` | `33225f31bae1` | `33225f31bae1` |

Release bytecode snapshot unchanged; `evm::differential` (2000 steps) green.

**Not measured.** N² threads was a bug in what `LITHE_THREADS` meant, not a slowdown these targets showed at N = 16 with few facets; no wall-clock claim is made for it. What it buys is that later multi-thread numbers mean what they say.

## S44 Per-build counters

**Plan.** `gen::EMITS`, `FINISHES`, `PROMOTE_ROUNDS` and the `*_NS` sums were process-global and never reset, so the second `build` in one process reported cumulative totals. Reset them per build, make `PROMOTE_ROUNDS` cover the same work as `PROMOTE_NS`, and let the harness parse a `[time]` line with no rounds group.

**What changed.**
- `gen::reset_timing()` zeroes all eight counters; `lib.rs::build` calls it first.
- The creation-code `promote` in `gen::creation` was untimed while `PROMOTE_NS` only counted the runtime emit's; it is now timed too, so `PROMOTE_NS` and `PROMOTE_ROUNDS` both cover every `Gen::promote` the build runs.
- `scripts/bench_compile.py`: the rounds group is optional in `TIME_LINE` and `promote_rounds` is `None` when absent, so a binary from before the counter still parses. Self-check covers both shapes.

**Proof.** `LITHE_TIME=1 target/fast/lithe abi` over three contracts in one process — the case that used to accumulate:

```
[time] check=145.452µs backend=1.047063ms | emits=1 sum=111.258µs (promote 75.591µs, 3 rounds) | ...
[time] check=57.227µs  backend=415.906µs  | emits=1 sum=27.291µs  (promote 13.996µs, 1 rounds) | ...
[time] check=308.766µs backend=1.297209ms | emits=1 sum=149.93µs  (promote 64.58µs,  4 rounds) | ...
```

`emits=1` on every line: each build reports its own work. Before, the second line would have read `emits=2`.

`python3 scripts/bench_compile.py --self-check` passes, including the new old-format case (`promote_rounds is None` when the group is missing). Bytecode-identical: release snapshot unchanged, `evm::differential` green.

**Tests, and one honest caveat about them.** `cargo test --lib` is green (553 passed, 2 ignored) at load average ~16 on 16 cores, and the bin suite is green (25 passed). At load 40–70 the same suite intermittently fails 1–4 tests in `evm::prove`, with Z3 answering "unknown": those tests give the solver a budget and the box was oversubscribed, and they pass in isolation in under a second and as a whole `evm::prove::` group (38 passed) on this tree. The baseline commit was checked the same way and is green at lower load, so this is machine contention, not a regression from either step; neither step touches `prove`.

**Caveat for the harness.** The counters are still process-wide, so `reset_timing` assumes one build at a time. That holds for `lithe compile <file>` and for a test building one contract, but `compile_dir` builds files on several threads, and there the reset races: on `/tmp/bd` (three contracts, one process, same work either way) `LITHE_TIME=1 lithe compile` printed `emits=1`, `emits=2`, `emits=2` at `LITHE_THREADS=8` and `emits=1` three times at `LITHE_THREADS=1`. So a parallel directory build's `[time]` lines are sums over whichever builds overlapped, not one build's. `bench_compile.py` measures one file per process, which is the case it reports and the case that is now correct. Fixing the parallel case needs thread-local counters, which is a separate step; this one is bytecode-identical and makes the single-build numbers trustworthy.

## S49 The `simplify:` list matches the meter

**Plan.** Two review findings on `ab6c382`'s doc-only diff. The warm-set bullet called precompiles 1–3 warm "by accident" beside "unrelated low addresses"; the seed is 1..=0x11, EIP-2929's precompile set, so those are warm by the spec's rule and no unrelated address is in it. The entry naming the real gaps (`0x100` and created accounts) was missing, and the created-account gap was also unlisted in the creation bullet. Both fixed in the prose, not the meter, so no gas total moves.

**What the code says.**
- `metered` seeds `from`, `to`, and `1..=0x11` (`src/evm/bench_gas.rs:147–150`); `charge` bills a call target 100 if `accounts` already holds it and 2 600 otherwise (`:120–128`). EIP-2929 warms the precompiles at a transaction's start, so that range is the rule, not an accident.
- `0xf0`/`0xf5` charge `32_000 + 2 * words` and never insert the created address (`:119`); only the call ops insert (`:121`). So the first call to a freshly created contract is billed the cold 2 600 where a node's CREATE warms the account. That is the gap the creation bullet now names.
- `0x100` P256VERIFY is answered by the interpreter (`src/evm/mod.rs:988`) but sits outside the seed, so its first call is cold too.
- Deployment is unaffected: each suite's deploy passes the new address as `to` to `metered` (`:460`), so it is warm, and the code deposit is added separately (`:467–471`).

**What changed.** Doc lines only, in `src/evm/bench_gas.rs`: the warm-set bullet states the seeded range as EIP-2929's precompile set and the P256VERIFY gap, and drops the "unrelated low addresses" claim; the creation bullet gains the created-account gap.

**Proof.** A comment-only diff cannot move bytecode or gas. Re-measured rather than asserted, `LITHE_BENCH_OUT` through `cargo test --lib evm::bench_gas` on this tree: 45 suites, transaction gas **68 121 662**, deploy gas **28 315 691**, suite runtime bytes **106 059** — the same three totals as `## 3.2c`'s after column, so the last codegen change's record still describes this tree and no number needs re-recording. `cargo test --profile fast --lib evm::bench_gas` green (2 passed), `cargo fmt --check` and `cargo clippy --profile fast --lib` clean.

## S37/S45 build state off the budget

**Plan.** Three pieces of build state were reached through a thread's own thread-locals, but `parallel_map` only carried `byte_gas` into a worker. So a candidate that ran on a spare worker saw `asm::track::on()` and `certify::wanted()` as false while the same candidate on the caller's thread saw them as true: `asm::optimize` takes the block-IR path instead of the tracked one, `finish` takes its `cacheable` path, and the body memo's guards are read differently. Meanwhile a worker held its unit of the budget until the pool end, and the `LITHE_TIME` counters were process statics that `reset_timing` zeroed under a parallel `compile_dir`, so the `[time]` lines in a directory build were sums over whichever builds overlapped.

**What changed.**
- `gen::parallel_map` gives the unit back as soon as its worker finds the queue drained: `work` takes the `Unit` by value and lets it drop on return, so a thread with nothing left to take is off the budget at once instead of at pool exit. The caller's own thread runs one `work(None)` and holds no unit, as before.
- A worker starts from the caller's state: `asm::with_byte_gas(byte_gas, …)` as before, plus `certify::certifying(true)` when the build certifies and `asm::track::start()` when it tracks. Both flags are read once, on the caller's thread, before any worker spawns.
- The `LITHE_TIME` counters are now a thread-local `Counts` (`src/gen/mod.rs:171–290`) instead of process statics; `time()`, `add_promote_rounds` and `Timer::drop` write the calling thread's, and a worker hands its `Counts` back to the pool, which adds them in spawn order. `reset_timing` zeroes the calling thread's only, so a parallel directory build no longer races. The hand-back is unconditional, not gated on `LITHE_TIME`: it is a thread-local copy, so a build's counts never depend on whether anyone reads them.
- A worker hands back its `Certs` too, so a facet certified on a worker thread reaches the proof of the build that pooled it. `Track` notes are not merged: they are keyed by the labels of the build that made them and only that thread reads them, exactly as at one thread.
- `lib.rs::build` prints the line from `gen::counts()`.

**Why it cannot regress bytecode.** Every added branch reads a flag that was already true on the thread that does the single-threaded build; propagating it only makes a pooled build take the same branch. No plan, pass or cost model changed. A worker's notes are not merged into the caller's `Track`: the marks are keyed by that build's own labels and only that thread reads them, exactly as at one thread.

**Proof.** `cargo test` green (556 lib + 25 bin + 1 doctest; one more lib test than the parent, the new `gen::a_pools_work_is_the_callers_build`). That test asserts both properties this step is about: every item of a pool sees the caller's `certifying`/`track` state, and the items' `emits` counts come back to the caller's thread. It is load-bearing — with the two propagation calls deleted it fails at `LITHE_THREADS=8`, which is how the old behaviour was confirmed. `LITHE_THREADS` = 1, 8 and 64 all pass it. `LITHE_THREADS` = 1 and 8 both green on `evm::prove::certifying_builds_emit_the_same_bytes` and on `evm::prove::facets_hooks_and_upgrades_prove_at_the_bytecode_level`, the certifying paths this step touches. Release bytecode snapshot unchanged (`evm::snapshot`, both modes). `LITHE_FUZZ_STEPS=2000 evm::differential` 5 green. `LITHE_VERIFY=1 cargo test --lib -- --test-threads=1` 556 green. `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings` clean.

The early release has no unit test: `spare()` is process-wide and cargo runs tests concurrently, so any assertion on the global count is racy (the first version of this test asserted `spare()` after a pool and failed only in the full suite, at `left: 10, right: 15`, exactly because other tests held units then). The property is instead kept by construction — `work` owns the `Unit`, so it drops when `work` returns, which is the last take — and by the nested-pool test above, which asserts peak concurrency never exceeds the budget while 8 outer items each run a pool of 4.

A four-contract directory build (`bank`, `brackets`, `builtins`, `collections`), `target/fast`, cache off, `LITHE_TIME=1`:

| | `emits` per line | `finishes` per line | lines printed |
|---|---|---|---|
| before, `LITHE_THREADS=8` | 4, 4, 4, 4 | 6, 7, 7, 8 | 4 |
| after, `LITHE_THREADS=8` | 1, 1, 1, 1 | 2, 2, 2, 2 | 4 |
| after, `LITHE_THREADS=1` | 1, 1, 1, 1 | 2, 2, 2, 2 | 4 |

`emits=4` on three lines before is the accumulation: each `reset_timing` wiped the others' counts. After, every line is one build's own work whatever the budget. The four output trees are byte-identical at 1 and 8 threads (`sha256` per artifact).

**Known flake, pre-existing and not from this step.** `LITHE_VERIFY=1 cargo test --lib` fails `evm::snapshot::release_bytecode_matches_snapshot{,_under_verify}` on `examples/verification/tracked_token.lithe:TrackedToken` whenever the suite runs with several threads and with `evm::differential` in the same process; it passes at `--test-threads=1`, at `LITHE_THREADS=1`, and with `evm::differential` skipped. The same failure, with the same three hashes, reproduces on the base commit `b8fc4fa` with this branch stashed, so it is not this step. The likely mechanism is next on this family: `split::facet`'s process-wide `BUILT` memo caches a facet keyed by `(program, opts)` alone, while `FORCE_STATIC_HEAP`/`FORCE_SPECIALIZE` (test-only thread-locals) change what that facet builds — so a facet built by a differential test under a forced knob is read back by the snapshot test. That is a test-harness isolation bug, not build state a real compile depends on, and fixing it means keying the memo by those flags; it is left for its own step rather than widened into this diff. **Fixed in S51; see that section.**

## S51 S37's findings, and `make check` green

**Plan.** Three defects S37 left. (a) The whole-suite `LITHE_VERIFY` failure at its cause: `split::facet`'s process-wide `BUILT` memo must not answer for a build whose codegen a test forced. (b) `parallel_map` must merge a pool's certificates in item order, not spawn order, so `Certs.loops/funcs/inlines/guards` are the same at `LITHE_THREADS=1` and N. (c) Worker `Track` notes must be handed back in item order, or the reason they are empty written down and tested. No expectation edited.

**What changed.**
- `gen::forced()` (`src/gen/mod.rs:359`): true when this thread has `FORCE_STATIC_HEAP` or `FORCE_SPECIALIZE` set. Always false outside `cfg(test)`, so a release compile cannot take the branch.
- `split::facet` (`src/split.rs:593`): the memo is `(!gen::forced()).then_some(memo)`, so a forced build neither reads nor inserts. This is the whole of (a) — the key already covers the program and the options, and the flags are thread-locals a process-wide key cannot see, so there is nothing to add to the key that would not be wrong for the next reader. The on-disk cache is already off under `cfg(test)` (`cache_entry` returns `None`), so the memo was the only path.
- `gen::parallel_map` (`src/gen/mod.rs:1229`): each item's `Certs` travels with its output in `done`, and the sort by item index happens before any merge, so `Certs.loops/funcs/inlines/guards/lost` read in item order. That is the order the items certify in at one thread, so a proof is the same at any `LITHE_THREADS`. The counter sums still merge in spawn order, which only decides floating-point rounding.
- Track notes: **not merged, and the reason is written down** at `src/gen/mod.rs:1222–1227`. A note is keyed by a label of the one build that wrote it, and only that build reads it; notes from item *i* would be read by item *i+1* on the same thread if left in place, and those labels belong to a different build. So `work` now takes the caller's track aside for the duration of the pool and puts it back untouched, and each item's own notes are dropped when its `f` returns. That is what one thread's caller does already — `build` starts a track, `codegen` takes it for its certificates, and nothing carries across builds — so 1 thread and N now agree. The new test pins that too: the caller's track comes back with the note it went in with, while the items' notes are gone.

**Why it cannot change bytecode.** (a) is `#[cfg(test)]`-only. (b) and (c) move where already-computed values are put; no plan, pass, cost model or emit path reads them, and the certificate order is one no single-threaded build could produce any other way.

**Proof.**
- `LITHE_VERIFY=1 cargo test --lib`: **558 passed, 0 failed, 2 ignored** (560 total, 2 more than before this step). Before it the same command read 554 passed and 2 failed of 558, both failures `evm::snapshot::release_bytecode_matches_snapshot{,_under_verify}` on `tracked_token.lithe:TrackedToken` (`ce0f4cd7…` expected, `cb8f6762…` got). That failure reproduced here at the branch tip before any edit, so the cause is the one the plan names.
- `split::tests::a_forced_facet_is_not_read_from_the_memo` (new): builds `examples/verification/tracked_token.lithe` plain, then with `FORCE_SPECIALIZE`, and asserts the facet hashes differ. It is load-bearing: with `let memo = Some(memo)` restored it fails, and the probe that found the mechanism showed the facet going 3738 → 3840 bytes under the knob. `FORCE_STATIC_HEAP` alone does not move this facet (3738 → 3738); both set moves it to 3862, which is why the test uses the knob that does.
- `gen::a_pools_certificates_read_in_item_order` (new): runs the same eight items twice, each made artificially slower the lower its index so the queue is drained out of order. Once straight through on the calling thread, which is what `LITHE_THREADS=1` does, and once through `parallel_map`. Asserts both certificate lists are the eight `LoopCert`s in item order, so the pool agrees with the sequential order, and that the caller's own `Track` comes back with the note it went in with. Load-bearing: with the merge moved back before the sort it fails with `["7","6",…,"0"]` against `["0",…,"7"]`. Green at `LITHE_THREADS=1` and unset (16 here).
- `cargo fmt --check` clean; `cargo clippy --offline --all-targets -- -D warnings` clean for the crate and `playground/`. Release bytecode snapshot unchanged (`evm::snapshot`, both modes).

**`make check`** (`LITHE_CACHE_DIR=` so no build is cached), run to completion on this tree, exit 0:

```
fmt      cargo fmt --check                            ok
         cd playground && cargo fmt --check           ok
clippy   cargo clippy --all-targets -- -D warnings    ok
         cd playground && cargo clippy --all-targets  ok
test     cargo test --locked                          ok  (558 lib + 25 bin + 1 doctest)
verify   LITHE_VERIFY=1 cargo test --locked           ok  (558 lib + 25 bin + 1 doctest)
diff     LITHE_FUZZ_STEPS=2000 ... evm::differential  ok  (5)
snapshot cargo test --locked --lib evm::snapshot      ok  (2)
bench    LITHE_BENCH_GAS=1 ... evm::bench_gas         ok  (2, ignored included)
wasm     cd playground && cargo build --release       ok
```

## S52 S51's residual findings

**Plan.** (a) The calling thread is also a pool worker, and its `take_certs` after each item swept certificates it made *before* the pool into whichever item it took first. Take those aside before the pool and keep them ahead of the item-ordered merge. (b) Run the one-thread arm of `a_pools_certificates_read_in_item_order` through the pool at a cap of one. (c) Hand `FORCE_STATIC_HEAP`/`FORCE_SPECIALIZE` to workers so `gen::forced()` is the caller's. No expectation edited. Both snapshots must stay unchanged.

**What changed** (`src/gen/mod.rs`).
- `parallel_map(items, f)` is now `pool(items, budget(), f)`. `pool` takes a thread cap that includes the caller. Below the cap, the spawn loop still claims from the process budget, so the public entry behaves as before.
- `pool` takes the caller's `Certs` before any item runs, when certifying. It keeps them first and then the items' certificates in item order. That is the order a one-thread build makes them in.
- A spawned worker sets both forced knobs from the caller's values. This is `#[cfg(test)]` code, like the knobs.

**Why it cannot change bytecode.** Moving certificates only changes where values that were already computed end up, and no pass reads them. The knobs exist only under `cfg(test)`. With cap = `budget()`, the spawn bound `min(items, budget)` is never tighter than the claims already allow.

**Proof.** Each new or changed test fails with its fix reverted (mutated and run, then restored):
- `gen::a_callers_certificates_stay_ahead_of_its_pool` (new). The caller holds a `"caller"` certificate. The pool runs eight items, and the lower an item's index, the slower it is. At cap 1 and at cap 8 the result must be `["caller","0",…,"7"]`. It fails at cap 8 without the take-aside, because the caller's certificate follows the item the caller's thread drained.
- `gen::a_pools_work_is_the_callers_build` gains a check: with `FORCE_SPECIALIZE` set, `forced()` is true in every item of a cap-8 pool. It fails without the propagation.
- `split::tests::a_forced_facet_built_in_a_pool_is_not_read_from_the_memo` (new). It builds `tracked_token`'s facet in four pool items, first plain and then forced. Every forced item must differ from the plain facet. It fails without the propagation: items on worker threads read the plain facet back from the memo. The S51 test never pooled, because that contract has a single facet.
- `gen::a_pools_certificates_read_in_item_order`. The one-thread arm is `pool(&items, 1, …)` and the other is `pool(&items, 8, …)`. Its assertions are unchanged.

**`make check`** (16 cores, `LITHE_THREADS` unset), exit 0. fmt and clippy are clean for the crate and `playground/`. `test` and `verify` each pass 560 lib tests (0 failed, 2 ignored), 25 bin tests and 1 doctest. `differential` at 2000 steps passes 5. `snapshot` passes 2, so both bytecode snapshots are unchanged. `bench_gas` passes 2, and the wasm playground builds.

## S27 Fx hashing

**Plan.** Make `asm`'s Fx hasher crate-visible and use it for every std `HashMap`/`HashSet` in `check`, `gen`, `route`, `split` and `index`. Use a `BTreeMap` wherever a map's iteration order reaches output. Bytecode must stay byte-identical.

**What changed.** `asm::{Fx, FxHashMap, FxHashSet}` are `pub(crate)`. Across `src/check/*`, `src/gen/*`, `route.rs`, `split.rs`, `index.rs` and `asm.rs`'s remaining std maps, `HashMap`/`HashSet` became the Fx aliases, and `::new()` became `::default()`. Three places stay std, on purpose:
- `gen::range`'s two maps keep their own `KeyHasher`.
- `route::render`/`render_footprints` take the selector map `lib.rs` builds.
- `asm`'s submodules (`marks`, `track`, `blocks`) are outside 5.4's list.

**Where order is seen.** `clippy::iter_over_hash_type` flags 21 `for` loops in these files (9 in `asm.rs`, over maps that were already Fx). A grep of `.iter()/.keys()/.values()` chains over the converted maps found the rest. Two sites reach output:
- `check::compose`'s `used`. Its iteration order picked which "unknown module" error is reported when several modules require missing ones. Under SipHash that error was random per process. It is now a `BTreeMap`, so the error is the first module by name.
- `index`'s `spelled`. Alias completions were pushed in map order, which the LSP returns as is. It is now a `BTreeMap`.

Every other site either sorts before use (`hash_set`, `hash_sorted`, `specs`, `funcs`, `outlined`, `named`, aliased completions), fills another map or set, or computes something order-independent (fixpoints, `any`/`all`, per-key assignments).

**Proof.** `make check` (16 cores). fmt and clippy are clean. `test` and `verify` each pass 560 lib tests (0 failed, 2 ignored), 25 bin tests and 1 doctest. `differential` at 2000 steps passes 5. `snapshot` passes 2, so **release and fast bytecode are byte-identical**. `bench_gas` passes 2, and the wasm playground builds.

The first `make check` run failed one test, `evm::prove::a_selfdestruct_sends_the_ether_away`. The solver ran out of time while a 16-core release build ran beside it. Rerun on an idle machine, every stage from `test` on passed.

**Timing.** Release binaries, parent `9c498a1` against this tree. `check` is the min of 9 `--fast` runs, interleaved, load ≈ 3:

| contract | `check` before | `check` after |
|---|---|---|
| erc20_full | 4.97 ms | 4.90 ms |
| erc1155 | 1.17 ms | 1.15 ms |
| uniswap_v2_pair | 0.519 ms | 0.509 ms |
| solady_erc20 | 0.230 ms | 0.226 ms |

erc20_full Release `backend` (3 runs each) went from 475–483 ms to 447–465 ms. That is within noise of the gen-side maps, and recorded rather than claimed.

## S40 3.3c priced

**Plan.** Price `Plan::batch` on against off for every plan the Release search builds. Delete the greedy `promote_region` path, the `batch = false` knob and `Move::Batch` only if batch wins or ties on all of them.

**How (S53: the instrument is in the tree).** `LITHE_PRICE_BATCH` set makes `codegen`'s `build_raw` (`src/gen/mod.rs`) build every plan the search asks for together with its `batch`-flipped twin, and print `[batch] on <cost> <bytes> <gas> off <cost> <bytes> <gas>` once per on/off pair to stderr (`cost` is `gas + bytes·byte_gas`, the search's own model). Unset, `build_raw` is one `OnceLock` read away from the old path. Twins only add entries to the emit and finish caches. The command, from a clean tree:

```
cargo build --profile fast --locked
for f in bench/*.lithe; do LITHE_CACHE_DIR= LITHE_PRICE_BATCH=1 target/fast/lithe compile $f --release 2>&1 >/dev/null | sed "s|^|$(basename $f .lithe) |"; done | awk '$2=="[batch]"{p[$1]++; P++; if($4<$8){w[$1]++;W++} else if($4>$8){l[$1]++;L++} else {t[$1]++;T++}} END{for(n in p) if(l[n]+w[n]) print n,p[n],w[n]+0,t[n]+0,l[n]+0; print "all",P,W,T,L}' | sort
```

The output is deterministic (two runs, identical). With the variable set, all 51 `--release` outputs are byte-identical to the run without it, so the twins do not move the search's result. `make check` is green: fmt, clippy, 560 lib + 25 bin + 1 doctest under both `test` and `verify`, the 2000-step differential (5), both snapshots unchanged (2), bench-gas (2), and wasm.

**Result: 1 140 on/off pairs. Batch wins 103, ties 1 015 and loses 22.**

| contract | pairs | wins | ties | losses | worst loss (cost, bytes, gas) |
|---|---|---|---|---|---|
| erc20_full | 96 | 72 | 12 | 12 | +199 (+0.10 %), −35 B, +374 |
| erc721 | 37 | 17 | 17 | 3 | +536 (+0.96 %), +42 B, +326 |
| erc721_full | 63 | 2 | 57 | 4 | +407 (+0.41 %), +30 B, +257 |
| fixed_point | 20 | 1 | 18 | 1 | +31 (+0.12 %), +5 B, +6 |
| uniswap_v2_factory | 46 | 0 | 45 | 1 | +94 (+0.07 %), +2 B, +68 |
| uniswap_v2_pair | 35 | 0 | 34 | 1 | +74 (+0.08 %), +4 B, +54 |
| erc1155 | 57 | 1 | 56 | 0 | — |
| staking | 37 | 10 | 27 | 0 | — |
| the other 43 | 749 | 0 | 749 | 0 | — |

**Against the S40 record (1 299 plans, 109/1 167/23).** Every worst-loss row is the same to the unit. The counts differ because the scratch build counted each plan the search asked for, so a pair the search requested from both sides (once with `batch` on, once via `Move::Batch`) counted twice. Keying the same run on the requested plan instead gives 1 242 / 107 / 1 112 / **23** — the recorded loss count exactly, with the erc20_full pair that loses counted from both sides. The remaining gap to 1 299 was not traced to a cause and is not claimed. The committed instrument counts each pair once, which is the comparison the decision is about.

**Decision, re-taken on the reproduced numbers: keep (not taken).** 22 pairs lose, so the deletion condition ("batch wins or ties everywhere") still fails. The greedy path is the cheaper plan in 22 places, so deleting it and the `Move::Batch` dimension would remove a choice the search can use. The Release emit count and time therefore stay as they are. With `Move::Batch` present, Release builds (emits/finishes, `backend`) measured: erc20_full 99/93, 461 ms; erc721_full 66/57, 178 ms; uniswap_v2_factory 50/41, 136 ms; uniswap_v2_pair 37/34, 130 ms; erc721 39/36, 73 ms; fixed_point 22/13, 52 ms.

What would close 3.3c instead: find why the batch walk loses on these plans. One untested hypothesis: the disjoint-walk rule in `region_batch` drops a region whenever its walk overlaps a taken one, so a lower-saving region can block a higher one that the greedy rounds would have reached later. A batch that replans the dropped words in a further round, rather than skipping them, should then tie or win everywhere.

## S48 3.3 closed: not taken

**Which of the two the tree satisfies: the second.** §5 3.3's value-numbering CFG scheduler (per-function live ranges, RPO block-entry layouts, spill at a part edge) is **not built**. 3.3 is recorded as not taken, on the measurement below. What the tree has instead is 3.3a (per-word region search) and 3.3b(ii) (batched regions, `Plan::batch`, priced by the search; see `## S40 3.3c priced` for the reproduced pricing).

**The measurement.** `promote`'s share of the backend on this tree, `target/fast`, `LITHE_THREADS=1`, cache off, load 16–19 (absolute times inflated; the shares are the point). Command:

```
for m in --fast --release; do for f in bench/*.lithe; do LITHE_CACHE_DIR= LITHE_TIME=1 LITHE_THREADS=1 target/fast/lithe compile $f $m 2>&1 >/dev/null | grep '^\[time\]'; done; done
for n in 16 64 128; do python3 scripts/gen_scaling.py $n > /tmp/ladder$n.lithe; LITHE_CACHE_DIR= LITHE_TIME=1 LITHE_THREADS=1 target/fast/lithe compile /tmp/ladder$n.lithe --fast 2>&1 >/dev/null | grep '^\[time\]'; done
```

| target | backend | `promote` | share | rounds per emit |
|---|---:|---:|---:|---:|
| all 51 `bench/`, Fast | 1 132 ms | 100 ms | 8.9 % | 11.3 |
| all 51 `bench/`, Release | 13 460 ms | 3 924 ms | 29.2 % | 17.1 |
| erc20_full Fast | 83 ms | 9.0 ms | 11 % | 58 |
| erc20_full Release | 4 602 ms | 1 690 ms | 37 % | 58 |
| ladder 16 / 64 / 128, Fast (min of 3) | 28 / 88 / 234 ms | 1.1 / 3.4 / 8.4 ms | 3–4 % | 4 / 4 / 4 |

**The three obligations §5 3.3 carries, answered from numbers already in this file.** No new run was needed: the S48 table gives the shares (taken at load 16–19, so its absolute ms are inflated), `## 3.2c`'s first table gives the absolute times at load 2.0, and `## 3.3b(ii)` gives the size and gas of the 3.3 slice that landed.

**1. Compile time.** What 3.3 delivered is 3.3a and 3.3b(ii): ladder 128 Fast `promote` 32.5 → 20.1 ms (3.3a, byte-identical) → 12.0 ms (3.3b(ii)), rounds 258 → 4, and rounds are now 4 at every ladder size. What the unbuilt scheduler could still add is bounded by `promote`'s remaining time, and that bound reaches none of the open compile-time targets:

- **erc20_full Fast ≤ 15 ms (§4, after Phase 3).** At load 2.0 the backend is 40.3 ms with `promote` 5.1 ms (`## 3.2c`). Deleting `promote` outright leaves 35.2 ms, still 2.3× the target; the rest is `optimize` (12.6 ms) and `outline+` (9.9 ms). The S48 share, 11 % of erc20_full and 8.9 % over all 51 `bench/` Fast, says the same.
- **Synthetic 1 735-line build ≤ 25 ms (§4).** That is ladder 64: backend 43.5 ms with `promote` 1.9 ms at load 2.0 (`## 3.2c`). Without `promote` it is 41.6 ms, still over.
- **3.5 (ladder linearity).** Closed: the 439→1735 per-line bar is met at 0.63× Fast and 0.90× Release. `promote` runs 4 rounds per emit on the ladder and is 3.6–4.5 % of the Fast backend there (11–17 % in Release, where the search pays it once per candidate); what is still superlinear above 1735 lines is `optimize`. See `## S50 3.5 closed`.
- **Release** has no compile-time target in §4. Its 29 % `promote` share is real, but it is paid per candidate at 17 rounds per emit (58 on erc20_full), so the lever is the round count, not a new algorithm (see "What would reopen it").

**2. Size and gas, the ≤ 1 % budget and its "expect improvement".** The codegen 3.3 landed is 3.3a (byte-identical) and 3.3b(ii); its gate is `## 3.3b(ii)`:

| measure | delta | budget |
|---|---:|---|
| runtime bytes, 272 target-modes | **−0.027 %** | within, and improved |
| creation + runtime, the 13 that change | −0.153 % | within, and improved |
| deploy gas, 45 suites | −0.060 % | within, and improved |
| gas including deploy | **−0.018 %** | within, and improved |
| transaction gas, 45 suites | **+0.0002 %** (+150 gas, `erc20_full` only) | within, **not** improved |

Every step's status and returndata hash is unchanged in all 45 suites. One per-target entry is over 1 %: `nft` Fast +1.4 %, the batched start plan's price in the mode that cannot decline it; Release leaves `nft` unchanged. So the §2 budget passes on totals and size and deploy gas improve as §5 expected, but transaction gas does not: it is flat to +0.0002 %. The improvement §5 expected from a scheduler with planned block-entry layouts is not delivered, because that scheduler is not built. The only stream-cutting variant measured, 3.3b(i), cost +4.1 % Fast / +4.6 % Release runtime bytes and was not taken. To land at all, a scheduler has to beat today's greedy on every knob (`tight`, `hold_dups`, `sink`, `abandon`, alias copies) within 1 % over every target-mode.

**3. Where the stack-too-deep guarantee lives.** §5 3.3 asked for a guarantee through spilling to the memory home. Without the scheduler there is no spill. The guarantee is instead that promotion never takes a word out of its home where an access would be out of reach:

- **Every local has a memory home.** `gen` places every local in memory, so the unpromoted stream is valid at any number of locals.
- **Every promotion rewrite checks reach.** `hold` only rewrites an access whose value is within 16 items (`src/asm.rs`, `(0..16).contains(&above)`). The checks in `plan_region` (`d < 16`), `walk_alias` (`d < 16`) and `abandon_walk` (`d >= 16` refuses) do the same. An out-of-reach access stays an `MLOAD`/`MSTORE` on the home.
- **The outliner obeys the same limit.** `run_effect` refuses a run that takes or leaves more than 16 items, `fetches` refuses one whose arguments sit deeper than 16, and `outline_once` refuses a prologue over 16.

The user-facing statement is `docs/src/pages/guide/architecture.mdx`, "Why stack-too-deep cannot occur". 3.3a and 3.3b(ii) changed which regions are chosen and how many are applied per round, not these checks. 3.3b(ii)'s `region_batch` takes only regions with disjoint walks, so each region's depths are the ones its plan computed. The `LITHE_VERIFY` oracle re-plans every taken word from scratch.

So the rewrite buys at most 5 ms of erc20_full's 40 ms Fast backend, closes no compile-time target, and risks the 1 % size gate. The guarantee it was to carry already holds without it. It is not taken.

**What would reopen it.** Spill-at-part-edge is untested. This record does not show it fails; it shows it does not pay against the open targets. Release's 58 rounds per emit on erc20_full is the cheaper lever: `region_batch` drops regions whose walks overlap, so real contracts still take 10–60 rounds where the ladder takes 4. Re-planning the dropped words in the same round is S40's open hypothesis. `LITHE_PRICE_BATCH` prices it with no extra tooling.

Nothing in codegen changed for this step, so both snapshots are unchanged.

## S23 4.1 closed: not taken

Plan: measure the one unit §5 4.1 can split after S48: the emitter's per-function bodies, before `resolve` joins them. Close 4.1 with that number if the split cannot pay or cannot be byte-identical cheaply. Proof: the new counter only reads the clock when `LITHE_TIME` is set, so bytecode does not change. Both snapshots are unchanged and `make check` is green.

**The instrument.** `gen::Counts::body_ns` (`Phase::Body`) times every `Gen::emit` and `Gen::emit_init`, the scouting passes in `codegen` included. This is all the emitter's own work, before `drop_unread_caches`, `promote`, and `resolve`. The `[time]` line ends in `| body X`. `scripts/bench_compile.py` parses it as `body_s`, and `None` on older lines; `--self-check` covers both. When `LITHE_TIME` is unset, `time()` still returns `None` before touching the clock.

**The measurement.** `target/release/lithe`, `LITHE_THREADS=1`, `LITHE_CACHE_DIR=` empty, min-of-3 `backend` per file, load 1.2–1.7. The command (sums use `scripts/bench_compile.py`'s `phases`):

```
python3 -c '
import os,subprocess,sys; sys.path.insert(0,"scripts"); from bench_compile import phases
mode,files=sys.argv[1],sys.argv[2:]; env=dict(os.environ,LITHE_TIME="1",LITHE_THREADS="1",LITHE_CACHE_DIR="")
run=lambda f: phases(subprocess.run(["target/release/lithe","compile",mode,f],env=env,capture_output=True,text=True).stderr)
rows=[min((run(f) for _ in range(3)),key=lambda p:p["backend_s"]) for f in files]
t=lambda k: sum(p[k] for p in rows); print(t("backend_s"),t("body_s"),t("promote_s"),t("finish_s"))
' --fast $(ls bench/*.lithe | grep -v uniswap_v2_factory)
```

I re-ran the command exactly as written, Fast, while `make check` was running (load 8.7). The absolute times were inflated (695 ms backend) and `body` came out at 8.8 %.

`uniswap_v2_factory` is left out. It is the only `bench/` file whose Fast build runs two emits, because it embeds `uniswap_v2_pair` as a peer build. That whole build runs inside the factory's `Gen::emit`, so `body` counts a complete backend: 21.8 of 23.0 ms Fast, 336 of 321 ms Release.

| target | backend | `body` | share | `promote` | `finish` | ceiling at ∞ threads |
|---|---:|---:|---:|---:|---:|---:|
| 50 `bench/`, Fast | 301.3 ms | 27.3 ms | **9.1 %** | 8.8 % | 71.2 % | **1.10×** |
| 50 `bench/`, Release | 4 187 ms | 342 ms | **8.2 %** | 29.1 % | 56.5 % | **1.09×** |
| erc20_full Fast / Release | 35.9 / 1 427 ms | 5.6 / 99.5 ms | 15.7 / 7.0 % | | | 1.19× / 1.08× |
| uniswap_v2_pair Fast / Release | 18.2 / 330 ms | 1.9 / 28.2 ms | 10.3 / 8.5 % | | | 1.11× / 1.09× |
| ladder 16 / 64 / 128, Fast | 10.8 / 40.8 / 107.9 ms | 0.8 / 5.3 / 17.5 ms | 7.4 / 12.9 / 16.2 % | | | ≤ 1.19× |
| ladder 16 / 64 / 128, Release | 21.1 / 129 / 432 ms | 4.5 / 32.5 / 106 ms | 21–25 % | | | ≤ 1.33× |

**Why this closes 4.1.** Each of its obligations, in turn:

- **Emit per function in parallel.** The bound is the `body` share. Fast, the mode §4's compile targets are written for, has at most 1.10× to gain over `bench/` and 1.19× on erc20_full, and that assumes unlimited threads and a join that costs nothing. Release reaches 21–25 % only on the ladder. Release builds already run their candidate plans in parallel across the same thread budget: erc20_full Release goes 1 848 → 624 ms from 1 to 16 threads on the tree this was measured on, and 1 438.2 → 452.7 ms on the finished branch (`## Comparison with baseline.json`). With `parallel_map` already using the threads, splitting each candidate's bodies adds no CPUs.
- **Schedule (`promote`) per function.** There is no per-function scheduler unit (S48). The only split measured, `promote` cut at function edges, costs +4.1 % Fast and +4.6 % Release runtime bytes (`## 3.3b(i)`). That is four times the §2 budget, and the loss comes from cutting the stream, not from tuning (`## 3.3b(i)`).
- **Optimize per function.** `optimize` takes `resolve`'s output, and `resolve` places every memory region using heat counted over the whole joined stream (`Gen::resolve` in `src/gen/plan.rs`). One function's addresses depend on every other function, so per-function input to `optimize` does not exist before the join. The cross-function passes it runs (`merge_tails`, `dedup_blocks`) and `outline` run on the joined stream anyway.
- **Deterministic, byte-identical join.** A body is not self-contained. Bodies take labels and memory spaces from shared counters. The first body that needs a helper (`subs`), a panic or raise stub, the error head, an embedded datum, or an early query creates it, and later bodies reuse it. The machinery that already re-installs one body in another build is `recall_body` (1.4's `BodyMemo`). It records 38 fields per body, and in 21 cases it declines rather than relocates: an earlier helper already exists, the embedded-data prefix differs, an early query moved, or the error head does not line up. A parallel join would have to handle all 21 by relocating instead of declining. That is a rewrite of the memo path, for a speedup of at most 1.10×.
- **Wasm fallback and determinism.** Nothing new runs in parallel, so the wasm build stays single-threaded and `make check`'s `wasm` target still builds the playground. With the existing candidate pool, `--release` output is byte-identical at `LITHE_THREADS=1` and `LITHE_THREADS=16` for all 51 `bench/*.lithe` and ladder 128 (sha256 of stdout per file).

**Reproducing the 1-vs-N answer (S55).** The test is a recorded command, not a `tests/` integration test. The thread budget is read once per process: `gen::thread_cap()` and `gen::budget()` are `OnceLock`s over `LITHE_THREADS`, so one test process cannot build at both 1 and N threads. A test that drove the binary would run the debug build's Release search on erc20_full twice in each of `make check`'s `test` and `verify` passes. The release binary does the whole check below in 3 s. Run it from the repo root after `cargo build --release --locked`. Factory goes through directory mode because `lithe compile` refuses a single file with two units ("one bytecode needs a single contract"):

```
L=$PWD/target/release/lithe; T=$(mktemp -d); python3 scripts/gen_scaling.py 128 > $T/ladder128.lithe
mkdir $T/f && cp examples/factory.lithe $T/f/
for mode in --fast --release; do for n in 1 16; do
  export LITHE_CACHE_DIR= LITHE_THREADS=$n
  a=$($L compile $mode bench/erc20_full.lithe | sha256sum | cut -c1-16)
  b=$($L compile $mode $T/ladder128.lithe | sha256sum | cut -c1-16)
  c=$(cd $T && rm -rf out && $L compile $mode f >/dev/null && cat out/f*/*.json | sha256sum | cut -c1-16)
  echo "$mode threads=$n erc20_full=$a ladder128=$b factory=$c"
done; done; rm -rf $T
```

Run at `a11e921` on 16 cores, load 2.5, 3.1 s wall:

| mode | threads | `bench/erc20_full.lithe` | ladder 128 | `examples/factory.lithe` (`Factory.json` + `Vault.json`) |
|---|---:|---|---|---|
| Fast | 1 | `869680db938303ac` | `280bf6115328624d` | `f181acbe1056d6cc` |
| Fast | 16 | `869680db938303ac` | `280bf6115328624d` | `f181acbe1056d6cc` |
| Release | 1 | `66e0cbebb7dcf7a6` | `280bf6115328624d` | `0844adae3a9c0581` |
| Release | 16 | `66e0cbebb7dcf7a6` | `280bf6115328624d` | `0844adae3a9c0581` |

Every digest is the same at 1 and 16 threads, so the re-run agrees with the claim above. On ladder 128, the Release search ends on the start plan's bytes, so its digest equals Fast's. `examples/factory.lithe` is in the list because it is the only file in `bench/`, `examples/` and `fuzz/` with two units. It is the evidence `## S24 4.2` relies on.

**What would reopen it.** Per-body emission growing to about a third of the Fast backend, so that the ceiling passes 1.5×. That could happen once `optimize`/`outline` (71 % of Fast) become linear: ladder 128 Fast is already at 16 %. The design would then be `recall_body` extended to relocate where it now declines, run on forks of one `Gen`, and joined in target order.

Tests: `make check` (fmt, clippy, test, verify, differential, snapshot, bench-gas, wasm); `python3 scripts/bench_compile.py --self-check`. Both snapshots are unchanged, because the change only reads the clock under `LITHE_TIME`.

## S24 4.2

Plan: overlap one sibling unit's `check` and `route::abi` with another's codegen by building a file's units on the existing pool. Proof: results come back in declaration order, a unit test compares them with one-at-a-time builds, and the S55 command compares digests at 1 and 16 threads. Expected number: none moves on this corpus (see "Payoff").

**The change** (`d38f65b`). `compile` (`src/lib.rs:190-217`) wraps each unit from `modules::split_units` in a `Mutex<Option<_>>` and hands the list to `gen::parallel_map`. Whichever worker reaches a unit takes it and runs `build`, which does `check` → `route::abi` → `route::method_ids` → `split::build_from`. So one sibling's check and ABI overlap another's codegen. `in_file` is applied to an error on the worker, and the pool returns results in declaration order, so the order of `contracts` and errors is the order the file declares them.

**Determinism.** The test is `sibling_units::pooled_build_matches_one_thread_in_order` (`src/lib.rs:2190`). It runs `compile` on `examples/factory.lithe` and compares each unit with a sequential `build` of the same unit: name, bytecode, deployed bytecode, method identifiers and warnings. For 1 vs N there is the binary-level command in `## S23 4.1 closed: not taken`, whose target list includes `examples/factory.lithe`. Directory mode, `LITHE_CACHE_DIR=` empty, 16 cores, load 2.5, sha256 of `out/factory.lithe/Factory.json` + `Vault.json`: Fast `f181acbe1056d6cc` and Release `0844adae3a9c0581`, identical at `LITHE_THREADS=1` and `16`. Those are the digests the S24 handoff reported, so the re-run agrees with it.

**What the test proves, and what it does not.** `gen::pool` spawns a worker only while `spawned.len() + 1 < items.len().min(cap)` and a budget unit can be claimed (`src/gen/mod.rs:1316`). At `LITHE_THREADS=1`, on one core, or when other pools in the test process hold the spare budget, the two units run inline and in order on the calling thread. The unit test therefore proves the bytes are equal, not that the units overlapped. Overlap happens only when a second thread is free, as in the 16-thread run of the command. That run checks bytes too; it does not time anything.

**Payoff.** None on this corpus, and none is claimed. Counting `contract` declarations across `bench/`, `examples/` and `fuzz/`, `examples/factory.lithe` has 2 and no other file has more than 1. (`examples/compose.lithe` matches the word twice, but one match is inside a comment.) For all 51 `bench/*.lithe` the pool gets one item and spawns nothing, so no benchmark number moves. The change pays only for future files with several units.

**`LITHE_TIME` with siblings.** Each pooled sibling runs its own `build` and prints its own `[time]` line (2 lines for factory). With a second thread those lines can come out in either order. `scripts/bench_compile.py::phases` sums `check_s` and `backend_s` across all matching lines, but takes `emits`, `finishes`, `promote`, `optimize`, `outline` and `body` from the last line only. So for a multi-unit file it reports summed check and backend wall time next to one sibling's counters, and which sibling depends on the race. No bytes move. Only the harness's per-file counters are affected, and on the current corpus only factory, which is not a `bench/` file.

Tests: `make check`. No code changed in this step, so both snapshots are unchanged.

## 5.1 Interning: scope measured

This step is real work but it is not one iteration's worth, and the reason is measurable rather than a matter of taste. Recorded here so the next iteration starts from the number instead of rediscovering it.

**What the step asks for.** `Symbol(u32)` plus a per-compilation interner, replacing `String` in `NameAt`, `Expr::{Ident, Field, Call}`, `TypeRef::Name`/`Apply`, the `name` of every declaration, `Checked.named`, and `domain_tys`. Diagnostics and bytecode must be identical.

**The measurement.** `Symbol` and `Names` were added to `src/ast.rs` and `NameAt.name` alone was flipped from `String` to `Symbol` (nothing else changed), then the compiler was asked what broke:

| file | errors | in this slice? |
|---|---:|---|
| `src/check/hooks.rs` | 30 | no |
| `src/index.rs` | 21 | yes |
| `src/modules.rs` | 18 | no |
| `src/parse.rs` | 17 | yes |
| `src/check/guards.rs` | 17 | no |
| `src/spec/mod.rs` | 15 | no |
| `src/resolve.rs` | 13 | yes |
| `src/split.rs` | 10 | yes |
| `src/check/compose.rs` | 8 | no |
| `src/prove/bytecode.rs`, `src/check/funcs.rs` | 6 each | no |
| `src/lib.rs`, `src/check/mod.rs` | 5 each | yes |
| `src/route.rs`, `src/lint.rs` | 3 each | `route.rs` no |
| `src/spec/instrument.rs`, `src/prove/funcs.rs`, `src/check/types.rs`, `src/gen/dispatch.rs` | 1–2 each | mostly no |
| **total** | **184** | **7 of 19 files are in this slice** |

One field, 184 sites, 12 files outside the slice. Flipping `Expr::Ident`, `Expr::Field`, and `Expr::Call` too — which the step requires — multiplies that: those three variants are matched in 43 files across `src/gen/` and `src/evm/`, and `src/evm/matrix.rs` and `src/evm/language.rs` are test harnesses whose expectations are the differential gate.

**The two constraints that make it a design decision, not a mechanical sweep.** Both are in `src/modules.rs`, which this slice does not own:

1. **The table has to be shared, not per file.** `append` (`src/modules.rs:922`) merges one parsed `Program`'s vectors into another's. If each file interned into a table of its own, every merged `Symbol` would need remapping, and `std_program`/`parse_cached` return `Program` clones from a process-wide cache keyed on the file alone — so the table cannot live next to the parse result without becoming part of that cache key. The interner therefore has to be threaded through `load_inner` and passed into `parse`, or the merge has to remap.
2. **Interning must be complete before anything is parsed.** `std/` and the import graph are parsed on demand inside the merge loop. A table that grows while `append` runs gives different symbols to the same text depending on import order, which breaks determinism the moment two files are compiled concurrently (`emit_dir`, phase 4).

**The payoff, and why it needs the step to finish before it shows.** The whole compile is `load` + `check`; on the LSP path the rest is now cached. `did_change_coalesces` at `--profile fast` on 2026-11-09, load average 2–5, `bench/erc20_full.lithe`:

| phase | Fast, this tree |
|---|---:|
| load (lex, parse, resolve, merge) | 2.8–13.8 ms |
| check | 18.1–30.0 ms |
| lint | 1.4–6.0 ms |
| index | ~0.2 µs (lazy, from 2.6) |

`check` dominates, so the interner only pays if it reaches the checker's own name maps (`named`, `domain_tys`, the `Scope` maps, `Checker.visiting`), not just the AST fields. That is the same 12 files again. Interning `NameAt` alone would be a large diff with no measurable effect, which §2 rules out as a failed iteration.

**What landed: nothing.** `Symbol`/`Names` and the `NameAt` flip were reverted; the tree is clean and green at `38b6eb9` (`cargo test --lib`: 552 passed, 2 ignored; `cargo fmt --check` clean; release snapshot unchanged). Writing 184 mostly-cosmetic call-site changes against files this slice does not own, with the table's lifetime still undecided, is how the shared `checked.source` cache key and the differential harness get broken silently.

**The split this step needs**, cheapest first, each independently green and byte-identical:

1. **5.1a — the table, no field changes.** Add `Symbol`/`Names` to `src/ast.rs` plus `Program.names`, thread it through `load_inner`, and prove determinism: the same text gets the same symbol across files and across `emit_dir` orderings, with a test. No AST field moves, so nothing breaks, and the lifetime question above is settled with a diff that cannot regress bytecode.
2. **5.1b — the AST fields.** Flip `NameAt`, `Expr::{Ident, Field, Call}`, and `TypeRef` in one pass, since a partial flip is the 184-error state measured above. This is the slice that touches `src/check/`, `src/gen/`, `src/prove/`, and `src/evm/`, and it needs a single owner for all of them.
3. **5.1c — the checker's maps.** `Checked.named` and `domain_tys` as `HashMap<Symbol, _>`, keeping `route.rs:1879` and `index.rs:661`'s ordering by sorting on `Names::get` so the ABI and hover output keep their order. This is where the measurable win is, and it should be measured against the `check` numbers above.

5.2 (`FileId`/`Span`) touches the same fields, so 5.1b and 5.2 should be one slice with one owner, in the order the parent plan already sets: 5.4 → 5.3 → 5.1 → 5.2.

## 5.1a The table

Landed. `src/ast.rs` gains `Symbol(u32)` and `Names`, the table it indexes, plus `Program.names: Arc<Names>`. No AST field moved, so every diagnostic string and every byte of codegen is untouched — `evm::snapshot` is byte-identical in both modes and the differential gate passes.

**The lifetime question 5.1 left open, answered.** One table per process, `Names::shared()`, behind a `OnceLock`. `std_program` and `ModuleCache::parsed` are process-wide caches keyed on a file and its content hash; if the table were per build, a `Program` cloned out of either cache would carry symbols from the build that parsed it. A per-build table would also have to become part of the cache key and would make a symbol depend on what the build parsed before it — the two constraints recorded above. One process-wide table satisfies both: a symbol is a pure function of its text, and `append` merges `Symbol`s without remapping.

**Threading.** `parse` takes `&Arc<Names>`; `Parser` holds it and interns from `ident`, the one place an identifier's text is read. `LoadEnv` carries the table for a whole `load_in`, `empty()` takes the unit's own table, and every other parse site (`parse_specs`, `resolve::INDEX`, `lint`, `spec::instrument`, `lib::declares_no_contract`, the `uses` scan) uses `Names::shared()`. `Program.names` records it on every program `parse` returns and on the merged unit.

**Determinism test.** `modules::tests::a_name_has_one_symbol_across_files_and_build_orders` loads two files that both name `count`, asserts one table across them, asserts the same symbol for the same text, and re-runs the loads in the other order on a second thread to prove the symbol does not depend on parse order (which is what `emit_dir` varies). `Arc::ptr_eq` against `Names::shared()` pins "one table per process", the property the parse caches need.

**The test is not vacuous, which needed its own check.** That test interns `"count"` itself, so it would still pass if `parse` never touched the table. `parse::tests::parsing_interns_each_identifier_once_into_the_given_table` covers that half: it parses one file into a private `Names`, asserts the table grew, parses a second file with the same identifiers and asserts it did not grow again. Deleting the `self.names.intern` call in `ident` makes it fail, which is how the assertion was checked.

**Directory builds are unchanged.** `lithe compile bench` (51 files) hashes identically to the parent binary at `ab6c382`, at `LITHE_THREADS=1` and `=8`, and both thread counts agree with each other; wall time at 1 and 8 threads is the same as the parent (376/89 ms vs 369/88 ms, median of 7). The process-wide mutex does not serialize parallel builds in practice: the critical section is a map lookup, and the whole of `bench/` is 90 ms.

**Cost.** Interning costs one mutex acquisition and one `String` copy per identifier. `lithe abi`, median of 15 runs, parent (`ab6c382`) → this branch: `erc20_full` 18.0 → 17.8 ms, `uniswap_v2_pair` 8.0 → 8.1 ms, `solady_erc20` 6.5 → 7.0 ms. Inside noise; no regression. The win is not here — it is in 5.1c, where the checker's maps stop hashing strings.

`simplify:` the table never shrinks, so a long-lived language server keeps every identifier it has seen. Dropping entries the caches no longer reference is the upgrade if that ever shows up in RSS.

Gates: `cargo test --locked` (555 lib + 25 bin + 1 doctest, green — one more lib test than the parent), `LITHE_VERIFY=1 cargo test --locked` (green), `LITHE_FUZZ_STEPS=2000` differential (5 green), `evm::snapshot` (both modes, byte-identical), `evm::bench_gas` (both green), `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check`, and the playground `cargo build --release --locked` plus its clippy and fmt. The `lithe compile bench` hash comparison above is the determinism evidence at the whole-directory level.

The step's remaining halves are unchanged: 5.1b flips `NameAt`, `Expr::{Ident, Field, Call}`, `TypeRef` in one pass (the 184-error state measured above), and 5.1c takes `Checked.named` and `domain_tys`.

## 6.1–6.4 Evaluated

Measured 2026-11-07, `target/fast`, cache off:

- **6.1 Startup.** `lithe --version`: 1.5 ms min / 1.9 ms median over 50 runs, against 0.17 / 0.25 ms for `/bin/true`. That is about 1.3 ms of process start for a 47 MB unstripped binary (release is stripped). It is small next to any compile (Fast erc20_full ≈ 44 ms backend). Not taken.
- **6.2 Assembler.** `assemble_marked` is already a least fixed point: every label push starts at one byte and widens monotonically. Candidate cost is computed once per finish (`Built.cost`), and `asm::cost` runs only twice per `outline` with `both`. Nothing to take.
- **6.3 Keccak memo.** With a temporary counter:
  - erc20_full release: 81 982 calls, 20.9 ms of a 1.9 s backend (1.1%).
  - erc20_full fast: 2 923 calls, 0.75 ms of 44 ms (1.7%).
  - uniswap_v2_pair release: 13 864 calls, 3.5 ms.

  A memo pays a hash and a key allocation per call against about 250 ns of hashing. It would save well under 1%. Not taken.
- **6.4 Incremental heat/flow.** After 3.2b, heat is 92 ms of erc20_full release (about 5% of the backend) and 42 ms of ladder 128. A block's heat depends on global structure: coldness, loop depth, and the topological order of entries. Recomputing one block would need a skeleton-keyed cache (labels, label pushes, exits, and `JUMPI` positions) and an exact invalidation argument. Taken in 3.2b(ii) as the skeleton-keyed `flow` cache, with a ~5% hit rate; the goal was missed the incremental way. 3.2c met it by calling `heat` half as often (1019 `merge_tails` calls instead of 1940 on erc20_full), which leaves the incremental cache unnecessary: measured after 3.2c, `merge_tails` including its `heat` is 96 ms of erc20_full Release and 7.8 ms of ladder 128.

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

Current status of 3.3b/3.3c is in State; this handoff is the original analysis.

Stack-too-deep cannot occur today either: every local has a memory home, and promotion rewrites a load or store only when the value is within 16 items (`d < 16` in `promote_region`/`hold`). Otherwise the access stays on the home. `docs/src/pages/guide/architecture.mdx` explains this.

## 3.3a Region search per word

Plan: make the greedy's rounds search only what the last round changed, keeping the bytes identical. Proof: old and new binaries emit the same bytes, plus both snapshots, `LITHE_VERIFY=1`, and the 2000-step differential.

What changed (`src/asm.rs`):

- **No whole-stream scan in `promote_region`.** Candidates come from each tracked word's stores in `Uses` and from the loops the word is used in. `RegionPlans::best` keeps each word's best region: its saving, its entry, and its place in the old scan order, so ties still go to the candidate the scan met first. A word is searched again only if the round changed it:
  - one of its plans was dropped or must be rechecked;
  - it has a use in the code `Runs::update` rescanned, or in the code that was replaced;
  - it is used in a loop that was found again, or in a loop whose head is in the rescanned code.

  Words with a known best go first and set a floor. The other words are searched in order of the most they could save (`3 + 2·loads + stores`), and the search stops once that falls below the floor. A word with nothing at or above a floor is remembered as such, and reused while the floor is no lower.
- **Straight promotions no longer clear `RegionPlans`.** They update it like a region does (`applied` with the words they changed). `alias_copies` reads its candidates from `Uses` instead of scanning the stream.
- **`RegionPlans.plans` is keyed by id in a map.** `applied` was walking one list per instruction id (about 24 500 on ladder 128) to update about 60 plans.
- **Oracle.** Under `LITHE_VERIFY`, each round also searches every word from scratch and asserts the same winner. The existing per-plan asserts still run.

Equivalence: `lithe compile --fast` and `--release` of every `bench/`, `examples/`, and `fuzz/` file, plus ladders 16, 64, and 128, give the same stdout from the parent binary and this one (211 files × 2 modes). `tests/snapshots/bytecode.json` is unchanged. Ladder rounds are unchanged: 34/130/258 at N = 16/64/128.

Timing: `target/fast`, Fast mode, `LITHE_THREADS=1`, cache off, `promote` sum, best of 3.

| ladder | rounds | promote old → new | per round old → new |
|---|---:|---:|---:|
| 16 | 34 | 1.49 → 0.66 ms | 44 → 19 µs |
| 64 | 130 | 13.8 → 6.1 ms | 106 → 47 µs |
| 128 | 258 | 32.5 → 20.1 ms | 126 → 78 µs |

**Not done: per-function `Runs`/`Uses`/`Live` arrays.** What is left of a round is linear in the stream. On ladder 128 that is about 78 µs, of which:

| part | µs |
|---|---:|
| `LabelIndex` and `Exits` updates | 21 |
| `Live::update` | 20 |
| `Runs`/`Uses`/`Loops` updates | 13 |
| `apply_edits` splicing the flat `Vec<Inst>` | 15 |
| `RegionPlans` id rebuild | ~5 |

Each of these is a shift or copy of positions after the splice, a few ns per instruction. So `promote` is still O(rounds × n), with a smaller constant: about 2× at N = 64 and 1.6× at N = 128. Per-function arrays alone would not remove this. `LabelIndex`, `Exits`, `RegionPlans` ids, and the code vector itself are absolute positions in one stream too. The fix is to give `promote` per-function code with relative positions. That is not byte-identical by construction: liveness, exits, and `reached_outside` look across functions. It belongs with 3.3b, which replaces these structures anyway.

Tests: `make check` passed:
- fmt and clippy `-D warnings`
- `cargo test --locked` (552 lib)
- `LITHE_VERIFY=1 cargo test`, which runs the new search oracle
- `LITHE_FUZZ_STEPS=2000` differential
- both snapshots
- bench-gas
- wasm

## 3.3b(i) Per-function `promote`: sound, faster, over budget

Plan: give `promote` per-function code with relative positions, so a splice shifts only its own function; add a from-scratch oracle per part; report the ladder-128 `promote` time and round count. Proof: `LITHE_FUZZ_STEPS=5000` differential, both snapshots, the prove tests, and the size/gas budget.

**The round counter that step asked for is in, and it is the reason the task exists.** `asm::promote` returns `(changed, rounds)`, `gen::PROMOTE_ROUNDS` sums it, and the `[time]` line carries it. `scripts/bench_compile.py` parses it as `promote_rounds` (its `--self-check` covers the new field). Rounds grow with function count, and every round scans the whole stream:

| ladder | lines | rounds | `promote`, Fast |
|---|---:|---:|---:|
| 16 | 439 | 34 | 2.6 ms |
| 64 | 1735 | 130 | 15–22 ms |
| 128 | 3463 | 258 | 50–76 ms |

So `promote` is O(rounds × n) with rounds ∝ n: quadratic in the number of functions. The Release search pays this per candidate: `bench/erc20_full.lithe` Release runs 5 274 rounds over 94 emits, about 56 rounds an emit.

**What was built.** `promote` splits the stream at every label `calls` names — each function compiled once, each helper — and promotes each part on its own with the old greedy, fresh-label state carried across parts so two parts cannot mint the same label. Nothing jumps into a part except through its start label, which is what makes the split well-defined. A `LITHE_VERIFY` oracle re-promotes each part from scratch and asserts the incremental result equals it. Two rules keep the parts sound:

- a label another part refers to is never held across (`LabelIndex.outer`), because that part arrives at a depth this one's walk cannot see;
- a memory word accessed in more than one part is not held on the stack at all, because a part sees only its own accesses and would drop a store the others read.

**Result: it works, and it cannot land as the default.** With the cut list forced empty the refactor reproduces the baseline byte-for-byte, both modes, so the split is faithful and not what moves bytes. With every cut it is:

- **Sound:** the 5000-step differential passes (`fast_matches_release`, `optimizer_preserves_behavior`, `static_heap_preserves_behavior`, `optimized_code_matches_reference`, `specialized_copies_preserve_behavior`), and so do the full suite (552 lib, 25 bin, 1 doctest) and both snapshots.
- **Faster:** ladder `promote` Fast 49 → 17 ms at N = 128, 15 → 4.3 ms at N = 64, 2.6 → 0.45 ms at N = 16. Rounds are unchanged (34/130/258), so the win is the per-round scan shrinking from the whole stream to one part.
- **Over budget:** runtime size grows by 3 656 bytes on 89 001 across all `bench/*.lithe`, **+4.1 % Fast / +4.6 % Release**. The 1 % gate is four times exceeded.

The size loss is the regions that span two functions: a word stored in one entry and read in another can no longer be held, and a region that walked across a call into a neighbouring part now stops at the part edge. Neither safety rule causes it — disabling both leaves the size delta unchanged, and a single cut on `uniswap_v2_pair` alone still costs +5.7 % Fast. So the cost is intrinsic to cutting the stream, not a tuning problem.

**Decision: not taken.** A codegen change that grows runtime code 4.6 % for a 3× `promote` win does not fit §2's budget, and `promote` is not the phase that decides 3.5 (`optimize` is). The mechanism is reverted; the round counter and the harness field stay, because every later attempt at 3.3b needs them. 3.3c stays blocked. What a real fix needs: keep every word promotable across a part boundary by spilling it to its memory home at the edge (the plan's own "spill" rule), rather than excluding it — that should recover the cross-part regions without the size loss, and it is the next thing to try.

Tests run on the reverted tree (round counter and harness only): `cargo test --locked` (552 lib, 25 bin, 1 doctest, 0 failed), `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check`, `python3 scripts/bench_compile.py --self-check`. The snapshot is unchanged, because the shipped diff changes no codegen.

## 3.3b(ii) Batched promotion: rounds stop growing with the function count

Plan: stop applying one region per round. Every word's best region is already known from `RegionPlans`; take every one whose walk stays clear of the others and apply them in a single pass. Proof: the same words, the same walks, no stream cut — so it cannot lose cross-part regions the way 3.3b(i)'s per-function split did. Expected effect: rounds from O(functions) to a constant, `promote` flat in N.

What changed (`src/asm.rs`):

- **`region_batch`.** After the per-word search, `promote_region` hands every word with a known saving to `region_batch`, best saving first, ties by the search's old order. Each word is planned on the current code and dropped if its walk would share code with a region already taken — holding a word keeps an extra item above the code it spans, so two regions across the same code would have found different depths. Disjoint regions are independent, so their edits compose in one `apply_edits`.
- **A fresh label per region.** `plan_region` now takes the label it may mint for a moved exit, where it used to read `labels.fresh` itself. Every accepted region gets its own, so two cannot name the same one.
- **`Promoted::Region` carries the words.** The incremental `Exits`/`Live`/`Runs` update after a round needs every word the round touched, not one.
- **The knob.** `Plan::batch`, on in the start plan, off via `Move::Batch(!p.batch)` so the search prices both on each candidate. With it off, `promote_region` is byte-for-byte the old greedy path.

Rounds and `promote` on the ladder, median of 5 interleaved runs, `target/fast`, Fast mode, `LITHE_THREADS=1`, cache off (machine load 14–30 from sibling worktrees, so absolute times are inflated; the ratio and the round count are the point):

| N | lines | rounds old → new | `promote` old → new |
|---|---:|---:|---:|
| 16 | 439 | 34 → 4 | 1.70 → 1.11 ms |
| 64 | 1 735 | 130 → 4 | 13.62 → 4.77 ms |
| 128 | 3 463 | 258 → 4 | 49.58 → 12.03 ms |

Rounds are now a constant 4 regardless of function count — the quadratic term is gone, which is the part 3.3a could not remove. **Ladders 16/64/128 are byte-identical before and after** in both modes, so on those targets this is a pure speed change.

**Size, over every target.** `bench/`, `examples/`, `examples/stdlib/`, `examples/uniswap_v2/`, `fuzz/` and the ladders, both modes, parent `38b6eb9` vs this change. Over those 272 target-modes 259 are byte-identical and 13 differ: 10 change length and are the 10 size changes below, and 3 keep their length while differing in a few instructions — `examples/options.lithe` Release (12 bytes of 1 125), `examples/stdlib/utils.lithe` Release (7 of 6 627) and `bench/erc721.lithe` Fast (227 of 3 061), all DUP/SWAP reorderings, i.e. the same words held in a different order because a batch round can hold a set the greedy reaches in a different sequence. A second sweep over all 245 `.lithe` files (490 target-modes) moves nothing outside these 13. The middle row is the same 272 target-modes with `Plan::batch` off, which is the pre-change `Fast` build exactly: with the knob off, all 136 `Fast` builds have the parent's bytes, so every `Fast` delta below is the batched start plan and nothing else.

| measure | old | new | delta |
|---|---:|---:|---:|
| runtime bytes, all 272 target-modes, parent → here | 395 015 | 394 909 | **−0.027 %** |
| runtime bytes, same set, `Plan::batch` off → on | 394 862 | 394 909 | +0.012 % |
| creation + runtime, the 13 target-modes whose code changes | 138 748 | 138 536 | **−0.153 %** |

Per changed target the sizes are ±0–2 bytes except two: `nft` Fast +74 and `utils` Fast +14, against `erc20_full` Release −158, `governance_token` Release −112, `raw_codec` Release −20, `pair` Release −8, `uniswap_v2/factory` Release −8, with `erc20_full` Fast +2, `governance_token` Fast +2 and `collectible` Release +2 at the rounding end. **Those `Fast` increases are the batched start plan's own price, not a search result.** `Fast` builds the start plan once and stops, so on `Fast` there is no candidate to reject it: the +74 on `nft` is 2 749 → 2 786 bytes of `Fast` code, `region_batch` applying several non-conflicting regions in one round instead of one per round. `Release` prices that knob against un-batched promotion and only ships it when it is the cheaper of the two: `nft` Release stays 2 649 bytes and `utils` Release 6 627 bytes whether the knob is on or off, so neither shows a byte of growth in the mode where the choice is measured. The `Release` rows are correspondingly small (−158 / −112 / −20 / −8 / −8 / +2); the one that grows, `collectible` +2, is the batched plan winning on the search's `gas + bytes*byte_gas` cost while costing two bytes, the trade the search is allowed to make. `nft` Fast is the only per-target entry over 1 %: +1.4 % of a 5 136-byte contract, in the mode this step deliberately made single-build.

Two record corrections in this table, since the earlier rows did not reproduce. It read "deployed bytes, all 272 target-modes 394 862 → 394 909"; 394 862 is the **`Plan::batch` off** total and 394 909 the **on** total, so that row compared the knob's two settings, not the parent with this change — the parent's runtime total is 395 015, and both are in the table now. Its second row, "creation + runtime, the 13 changed targets 167 568 → 167 364", does not reproduce from this tree: the 13 snapshot keys read 138 748 → 138 536, the 13 with `Plan::batch` off 138 442 → 138 536, and the 10 size-changed files in both modes 190 712 → 190 500. It is replaced with the 13-key figure, which is what the sentence under it describes.

So `nft` Fast's +1.4 % stands as a per-target entry over the 1 % line, written down rather than averaged away. The §2 budget is on totals and passes on both readings: runtime bytes −0.027 % over the 272 target-modes, and −0.153 % creation + runtime over the 13 whose code changes, where the `Release` wins (−304 bytes) outweigh the `Fast` losses (+92).

**Gas, `evm::bench_gas`, all 45 suites, identical binaries to the snapshot.** Exactly one suite's numbers move; every step's status and returndata hash is unchanged in all 45. The rows carry the same names and scopes as 3.2c's and 1.2's tables: *transaction gas* sums each suite's steps, *deploy gas* is what putting the contracts down costs, *gas including deploy* is their sum.

| measure | old | new | delta |
|---|---:|---:|---:|
| transaction gas, 45 suites | 68 121 512 | 68 121 662 | **+0.0002 %** |
| deploy gas, 45 suites | 28 332 749 | 28 315 691 | −0.060 % |
| gas including deploy | 96 454 261 | 96 437 353 | **−0.018 %** |
| suite runtime bytes | 106 138 | 106 059 | −0.074 % |

The only suite that moves is `erc20_full`: suite runtime 8 235 → 8 156 bytes, deploy gas 2 127 472 → 2 110 414 (−17 058), transaction gas 6 789 696 → 6 789 846 (+150). Its Release code is 79 bytes smaller in both creation and runtime, so the cheaper deployment is the size; the steps cost 150 more.

So the two figures the record carried are the same measurement at different scopes, and both belong: **transaction gas +0.0002 %** is what `## State` called "total runtime gas", and **gas including deploy −0.018 %** is this table's total. Neither corrects the other — the deploy side carries the win (−17 058 gas, and −0.060 % over 45 suites), and it is invisible if only the step totals are summed.

Tests: `cargo test --locked` (552 lib, 25 bin, 1 doctest, 0 failed); `LITHE_VERIFY=1` with `LITHE_FUZZ_STEPS=5000` over the whole lib suite (552 passed) — the new `region_batch` oracle re-plans each taken word from scratch and asserts the saving that selected it, and the existing incremental-vs-fresh assertions cover every round; `evm::differential` at 5 000 steps (5 passed); `evm::prove` (55 passed, including the three bytecode proofs); both snapshots regenerated (13 of 290 keys change, each justified above); `cargo clippy --all-targets -- -D warnings`; `cargo fmt --check`; the playground wasm build; `scripts/bench_compile.py --self-check`. Determinism: `LITHE_THREADS=1/4/16` on ladder 128 Release give identical bytes.

**One flake, recorded honestly.** `evm::prove::facets_hooks_and_upgrades_prove_at_the_bytecode_level` failed once in a 5000-step verify run at machine load 38–52 and passed on rerun and on the final 552-test run. Its three inputs (`examples/verification/split_counter`, `tracked_token`, `upgradeable_counter`) are byte-identical before and after this change, so the prover is given the same code the baseline passes; the failure is a solver timeout under load, not a result. The baseline tree passes the same suite on an idle box.

## 3.4 Outline without per-site splices

Plan: write every call site of a round in one pass over the stream, not with one `Vec::splice` per site. Proof: old and new binaries emit the same bytes. Expected effect: the O(sites × n) term within a round goes away.

Profiling `outline_once` showed that `repeats` already refines groups of equal token runs one length at a time, with radix buckets by next token. That is the "hashed token runs" this task asked for, and it is linear in the stream times the lengths that survive. The quadratic part was the edit loop. Each of a round's call sites (511 on ladder 128) spliced the whole stream and the token arrays. That loop took 0.9 ms of a 6 ms round. Now return labels and tokens are assigned in the same order as before (last site first), and code, tokens, and sizes are rebuilt once. `outline` still runs on the flat stream. Moving it onto `Blocks` would add a conversion and save nothing: it runs once per finish, after `optimize` has already written the stream.

Equivalence: `lithe compile --fast` and `--release` on every `bench/`, `examples/`, and `fuzz/` file, plus ladders 64 and 128, produce identical stdout from the parent binary and this one (254 compiles plus 4 ladder builds). `tests/snapshots/bytecode.json` is unchanged.

Timing, `outline+` from `LITHE_TIME`, best of 5, `target/fast`, `LITHE_THREADS=1`, old → new:

| target | fast | release |
|---|---:|---:|
| ladder 128 | 27.8 → 29.8 ms | 28.4 → 26.8 ms |
| erc20_full | 10.6 → 10.4 ms | 482 → 478 ms |

The difference is noise on these targets. `outline+` is mostly the `optimize` and `finish` that run after outlining. The change removes the per-site splice term. It does not move the headline numbers.

**What remains O(n) per round.** `outline` loops `outline_once` until nothing is left, and every round does O(n) work over the whole stream: `safe_exits`, the `JUMPI` retokenisation, `flow`, prefix sizes, `repeats`, and the rebuild. At the time of 3.4, the exact-copy pass (`params = false`), which Release runs through `both`, applied only the single best outline per round, so its round count grew with the number of distinct repeated runs. 3.4b removed that: it now takes every non-conflicting run per round, so the round count is a handful and the remaining cost is those per-round O(n) terms.

## 3.4b Several exact-copy outlines per round

Plan: the exact-copy pass (`params = false`) takes every run that stays clear of the better ones in a round, as the parameterised pass already did, instead of only the single best. Proof: both snapshots, the ladder bytes, the full test suite. Expected effect: fewer `outline_once` rounds in Release.

`outline_once` now has one selection path for both passes: every run saving at least a quarter of the best, best first, skipping runs with a copy inside one already taken. The parameterised pass is unchanged; the exact pass loses its `best`-only branch.

Rounds of the exact pass, old → new (`LITHE_THREADS=1`, Release, the finishes that run it), measured at `fc4921d`:

| target | rounds | `outline_once` loop |
|---|---:|---:|
| erc20_full | 8 → 3, 7 → 1 | 4.1 → 2.9 ms, 0.77 → 0.39 ms |
| uniswap_v2_factory | 13 → 2 | 2.9 → 2.0 ms |
| erc1155 | 15 → 4, 3 → 2 | 5.1 → 2.7 ms, 0.17 → 0.19 ms |
| ladder 128 | 6 → 2 | 6.6 → 3.0 ms |
| ladder 256 | 8 → 3 | 19.3 → 10.2 ms |

The parameterised pass already ran 2–5 rounds. With both passes bounded to a handful of rounds, `outline`'s loop is O(n) times a small constant, so the per-round O(n) terms stay and making `flow`/prefix sizes incremental was not done. Release `outline+` on erc20_full (448 → 441 ms) barely moves: the exact pass runs only in the 2 finishes with `both`, and `outline+` is dominated by the 91 parameterised finishes' `optimize` after outlining and `finish`.

Bytes: `tests/snapshots/bytecode.json` is unchanged (`evm::snapshot`, both modes and under `LITHE_VERIFY`), and ladders 16/64/128/256 in Release give identical output from the old and new binaries. The exact pass's own output does change on some targets (it now outlines several runs per round), but on every target that changed program still loses to the parameterised one in `outline`'s cost comparison, so the emitted bytes are not a codegen change and the 5000-step differential and gas gate do not apply; `bench_gas` replays the identical bytecode. `cargo test --release` (552 passed), `cargo clippy --all-targets -D warnings`, `cargo fmt --check` pass.

### 3.4b re-verified at `3a670f0`

3.2b, 3.2b(ii), and 3.2c landed after `fc4921d` and rewrote `flow_`'s cold fixpoint and latch walk and `merge_tails`' pair selection, so both the round counts and the "incremental is not worth it" argument were re-measured at the merged head. `src/asm.rs` between `fc4921d` and `3a670f0` differs only inside `flow_` (13 lines); none of `outline_once`, `repeats`, or `outline`.

Rounds and loop time of the exact pass at `3a670f0`, with the counterfactual being 3.4b's own change reverted (`chosen.truncate(1)` for `params = false` only), temporary instrumentation, `LITHE_THREADS=1`, Release, `target/fast`, one binary:

| target | rounds old → new | loop old → new |
|---|---|---:|
| erc20_full (largest) | 7 → 2 | 5.8 → 1.8 ms |
| erc1155 | 15 → 4 | 30.3 → 3.3 ms |
| uniswap_v2_pair | 13 → 3 | 12.2 → 3.7 ms |
| uniswap_v2_factory | 13 → 2 | 10.7 → 4.9 ms |
| ladder 128 | 6 → 2 | 23.1 → 10.5 ms |
| ladder 256 | 8 → 3 | 79.9 → 34.3 ms |

The exact pass stays at 0–4 rounds, as recorded, and the parameterised pass at 2–5: the bound holds on the merged tree.

Bytes: all 51 `bench/*.lithe` plus ladders 64 and 128 give identical creation and runtime output under the two selection paths, in Release **and** in Fast (53 targets, 0 differ in either mode). The counterfactual's intermediate program does differ, and it is always rejected by `outline`'s `cost` comparison, so this is still not a codegen change: snapshot unchanged, gas gate not applicable. `evm::snapshot` (both tests, including under verify) green at `3a670f0`.

**Why incremental `flow` was not taken.** `outline_once` calls `flow` once per round; the other O(n) terms are the `JUMPI` retokenisation, the prefix-size build, `repeats`, and the rebuild. Measured over one full compile, summing every `outline_once` call (machine load 11–20 from sibling worktrees, so absolute times here are inflated; the share is the point):

| target | `outline_once` calls | loop | `flow` | `flow` share |
|---|---:|---:|---:|---:|
| erc20_full | 389 | 298.6 ms | 31.9 ms | 11% |
| erc1155 | 255 | 189.2 ms | 16.1 ms | 9% |
| uniswap_v2_pair | 137 | 71.1 ms | 7.3 ms | 10% |
| ladder 128 | 9 | 22.6 ms | 2.6 ms | 12% |
| ladder 256 | 13 | 53.4 ms | 6.5 ms | 12% |

Making `flow` free would save 10–12% of a loop that is itself a small part of `outline+`: in the same run, erc20_full's `outline+` was 1.13 s and its whole `outline_once` work was 0.30 s, so the ceiling is a few tens of milliseconds of a multi-second build. An incremental `flow` also needs the cross-round invalidation argument that 3.2b(ii) already found unnecessary at a 5% hit rate. Not taken, with that measurement as the justification.

## 3.5 Ladder after 3.4b

`python3 scripts/bench_compile.py --skip-gas --threads 1 --only scaling/nN.lithe`, cache off, `LITHE_THREADS=1`, 16 cores; Fast through a wrapper that passes `--fast`. Tree: 3.3a in part, 3.4b; 3.2b and 3.3b are not in it.

| N | lines | F promote ms | F optimize ms | F µs/line (p+o) | R promote ms | R optimize ms | R µs/line (p+o) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 439 | 0.9 | 7.6 | 19.2 | 6.0 | 9.2 | 34.5 |
| 32 | 871 | 1.7 | 17.8 | 22.3 | 16.6 | 17.7 | 39.3 |
| 64 | 1735 | 6.5 | 67.9 | 42.9 | 52.2 | 68.1 | 69.3 |
| 128 | 3463 | 20.1 | 352.1 | 107.5 | 200.6 | 355.0 | 160.4 |
| 256 | 6919 | 73.2 | 2208.2 | 329.7 | 727.9 | 2249.0 | 430.3 |

Per-line `promote`+`optimize` ratio, Fast: 439→1735 **2.23×**, 1735→3463 **2.51×**, 3463→6919 3.07×. Release: 2.01×, 2.31×, 2.68×. **The 1.5× bar is not met** *on this tree*. The 1.37× quoted in the comparison below is per-line *wall* time (Fast wall 22.1 → 115.5 ms is 1.32× now), not `promote`+`optimize`. Fast `promote` is close to linear (2.1 → 3.7 µs/line from 439 to 1735); `optimize` is the superlinear term (17 → 20 → 39 → 102 → 319 µs/line from N = 16 to 256), and its largest pass is `merge_tails` recomputing `heat` per call (3.2b, sibling workspace). 3.4b does not move these numbers: `outline` is 10 ms of ladder 64 and 27 ms of ladder 128. **Superseded: 3.2b and 3.3b landed after this table and the tree now meets the bar at 0.63× Fast and 0.90× Release. See `## S50 3.5 closed` for the re-run; this table is kept because it is the "before" of that record.**

## Comparison with baseline.json

The final refresh (S43), on the finished branch. Commit `6646998`, `target/release/lithe` (fat LTO, the release profile §4 asks for), 16 cores, one file per process, `LITHE_CACHE_DIR` empty so every row is a real compile. "base" is `baseline.json`, taken at `796fdfe` on the same box. **R** is Release and **F** is Fast; `(1)` is `LITHE_THREADS=1` and `(16)` is every core. Release rows are `python3 scripts/bench_compile.py` unchanged; Fast rows are the same script with `--bin` pointed at a two-line `execv` wrapper that rewrites `--release` to `--fast`, plus `--skip-gas`, which is how 1.2 and 3.5 took theirs and keeps the CLI's own default out of the comparison. (This is the final-refresh obligation the plan labels S43; `## S43 One thread budget` is a different step that shares the label.)

Five full rounds of each mode, each figure the minimum of its five. The spread across rounds on the 127-target total is 0.75 % Release at one thread (13.29–13.39 s), 0.76 % Release at 16, 2.9 % Fast (2.09–2.15 s) and 3.8 % Fast at 16. Wall time includes process startup, which is 4–6 ms of every row and most of why a Fast row on a 14-line file reads 5.9 ms rather than 2. Gas in release mode was identical in all five rounds. The one-minute load average on 16 cores was 0.2–2.0 at every round's start and end; the 15-minute figure was 14–18 from sibling worktrees, which is why these are minima.

This replaces the mid-branch snapshot taken at `9ec81c7`, which said of itself that 3.2b, 3.3, 3.5 and phases 4–6 were missing and that it should be re-run when they landed. They have all landed, and its rows are deleted rather than kept beside these because they measured a different tree; its headline numbers (18.6 s Release, 5.0 s Fast, the 1.37× ladder ratio, "Release bytecode and gas identical") are superseded by the ones below.

**A method note the Fast column depends on.** The `--bin` wrapper has to be cheap, because its own startup is inside the wall time. Three rounds taken through a Python wrapper read 5–6 ms higher on the small files than the same binary through a compiled one (`bench/counter` 11.9 ms against 6.3, `bench/env` 10.9 against 5.8), which is the interpreter's startup and nothing else. The five rounds reported here all use a small C wrapper that rewrites `--release` to `--fast` and calls `execv`, so what they measure is the compiler. The Python rounds are not used for any figure in this table.

### Every `bench/` contract, both modes, 1 and N threads

| target | lines | base R ms (1) | R ms (1) | R ms (16) | F ms (1) | F ms (16) | base runtime | R runtime | F runtime | Δ release runtime |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `bench/base64.lithe` | 14 | 7.6 | 6.7 | 8.1 | 5.9 | 5.7 | 891 | 891 | 874 | 0 |
| `bench/book.lithe` | 35 | 11.7 | 11.9 | 12.3 | 9.2 | 8.9 | 1160 | 1160 | 1091 | 0 |
| `bench/codec.lithe` | 69 | 52.2 | 49.7 | 42.6 | 17.3 | 18.4 | 2596 | 2613 | 2646 | +17 |
| `bench/collections.lithe` | 43 | 15.3 | 13.4 | 12.6 | 7.6 | 8.3 | 627 | 627 | 636 | 0 |
| `bench/counter.lithe` | 48 | 7.3 | 6.2 | 6.8 | 6.3 | 5.5 | 198 | 198 | 198 | 0 |
| `bench/date_time.lithe` | 57 | 70.7 | 67.8 | 44.2 | 8.3 | 8.3 | 1166 | 1166 | 1152 | 0 |
| `bench/deployers.lithe` | 69 | 64.1 | 63.2 | 38.5 | 10.9 | 11.1 | 1503 | 1503 | 1554 | 0 |
| `bench/dialer.lithe` | 52 | 18.1 | 18.3 | 18.0 | 9.3 | 9.2 | 1401 | 1401 | 1383 | 0 |
| `bench/env.lithe` | 16 | 5.1 | 5.4 | 5.5 | 5.8 | 5.9 | 81 | 81 | 81 | 0 |
| `bench/erc1155.lithe` | 158 | 590.0 | 546.5 | 219.4 | 26.0 | 27.4 | 5013 | 5026 | 4747 | +13 |
| `bench/erc20.lithe` | 99 | 121.2 | 93.1 | 50.5 | 10.6 | 11.1 | 2244 | 2269 | 2042 | +25 |
| `bench/erc20_full.lithe` | 183 | 1731.9 | 1438.2 | 452.7 | 50.4 | 50.7 | 7382 | 7334 | 7426 | −48 |
| `bench/erc4626.lithe` | 24 | 226.0 | 210.5 | 98.1 | 18.5 | 18.2 | 2884 | 2821 | 3063 | −63 |
| `bench/erc6909.lithe` | 68 | 159.2 | 133.8 | 61.6 | 16.0 | 16.6 | 3326 | 3423 | 3275 | +97 |
| `bench/erc721.lithe` | 119 | 159.2 | 147.5 | 69.4 | 17.4 | 16.6 | 3074 | 3081 | 3061 | +7 |
| `bench/erc721_full.lithe` | 176 | 503.4 | 476.1 | 184.2 | 27.3 | 27.2 | 5640 | 5624 | 5671 | −16 |
| `bench/exchange.lithe` | 51 | 9.8 | 8.9 | 9.4 | 6.8 | 6.8 | 417 | 417 | 442 | 0 |
| `bench/executor.lithe` | 115 | 16.3 | 16.8 | 14.9 | 8.3 | 8.5 | 807 | 807 | 822 | 0 |
| `bench/fixed_point.lithe` | 60 | 98.7 | 98.4 | 57.9 | 22.4 | 22.5 | 2831 | 2831 | 2918 | 0 |
| `bench/flash_borrower.lithe` | 55 | 15.6 | 15.6 | 15.6 | 8.6 | 8.6 | 822 | 822 | 871 | 0 |
| `bench/layout.lithe` | 64 | 7.0 | 7.0 | 7.7 | 6.6 | 6.5 | 705 | 705 | 705 | 0 |
| `bench/lists.lithe` | 68 | 18.9 | 17.2 | 16.8 | 8.4 | 8.5 | 1624 | 1624 | 1599 | 0 |
| `bench/logs.lithe` | 42 | 6.9 | 6.6 | 7.4 | 6.9 | 5.9 | 277 | 277 | 305 | 0 |
| `bench/loops.lithe` | 84 | 13.3 | 13.4 | 11.8 | 8.1 | 7.6 | 871 | 871 | 874 | 0 |
| `bench/math.lithe` | 24 | 6.5 | 6.1 | 6.8 | 6.9 | 6.1 | 424 | 424 | 424 | 0 |
| `bench/names.lithe` | 58 | 15.2 | 15.5 | 15.3 | 8.8 | 9.0 | 1312 | 1312 | 1289 | 0 |
| `bench/numerics.lithe` | 43 | 39.7 | 36.7 | 34.5 | 14.3 | 14.7 | 1679 | 1679 | 1702 | 0 |
| `bench/overloads.lithe` | 73 | 17.4 | 15.3 | 15.6 | 6.8 | 6.8 | 458 | 458 | 449 | 0 |
| `bench/ownable_roles.lithe` | 54 | 27.6 | 25.8 | 20.2 | 8.9 | 8.3 | 952 | 952 | 975 | 0 |
| `bench/profile.lithe` | 26 | 8.6 | 8.4 | 9.0 | 7.2 | 7.2 | 586 | 586 | 584 | 0 |
| `bench/reasons.lithe` | 80 | 10.8 | 10.7 | 10.3 | 6.6 | 6.7 | 844 | 844 | 845 | 0 |
| `bench/receiver.lithe` | 40 | 11.3 | 9.4 | 10.5 | 7.4 | 7.4 | 454 | 454 | 473 | 0 |
| `bench/receiver1155.lithe` | 76 | 18.8 | 15.8 | 15.5 | 7.8 | 8.1 | 926 | 926 | 944 | 0 |
| `bench/records.lithe` | 125 | 31.8 | 27.9 | 22.1 | 10.4 | 10.4 | 1508 | 1508 | 1508 | 0 |
| `bench/registry.lithe` | 68 | 13.9 | 12.3 | 12.6 | 8.3 | 8.3 | 1034 | 1034 | 1028 | 0 |
| `bench/relay.lithe` | 42 | 24.3 | 22.4 | 22.0 | 11.1 | 11.3 | 1886 | 1886 | 1828 | 0 |
| `bench/safe_erc20.lithe` | 29 | 11.7 | 10.3 | 10.2 | 7.2 | 7.1 | 543 | 543 | 543 | 0 |
| `bench/selectors.lithe` | 46 | 10.6 | 9.1 | 10.1 | 5.9 | 5.9 | 399 | 399 | 449 | 0 |
| `bench/shapes.lithe` | 86 | 17.9 | 17.8 | 17.1 | 8.7 | 9.1 | 1306 | 1306 | 1340 | 0 |
| `bench/solady_erc1155.lithe` | 249 | 91.7 | 87.3 | 55.6 | 14.8 | 15.4 | 2707 | 2707 | 2630 | 0 |
| `bench/solady_erc20.lithe` | 176 | 40.2 | 36.7 | 25.6 | 8.9 | 8.7 | 1395 | 1395 | 1402 | 0 |
| `bench/solady_erc721.lithe` | 241 | 67.6 | 64.4 | 42.0 | 12.7 | 13.3 | 2110 | 2110 | 2151 | 0 |
| `bench/staking.lithe` | 239 | 104.5 | 103.9 | 52.8 | 12.8 | 11.7 | 2486 | 2486 | 2177 | 0 |
| `bench/strings.lithe` | 70 | 17.2 | 15.5 | 15.9 | 10.9 | 11.8 | 1724 | 1724 | 1695 | 0 |
| `bench/tally.lithe` | 58 | 6.2 | 5.2 | 6.0 | 4.2 | 4.3 | 439 | 439 | 439 | 0 |
| `bench/texts.lithe` | 127 | 69.6 | 68.5 | 58.2 | 22.6 | 23.5 | 4105 | 4105 | 3911 | 0 |
| `bench/token.lithe` | 70 | 11.4 | 8.0 | 9.1 | 6.3 | 6.5 | 357 | 357 | 397 | 0 |
| `bench/traits.lithe` | 45 | 8.3 | 7.1 | 7.6 | 6.2 | 6.6 | 468 | 468 | 468 | 0 |
| `bench/uniswap_v2_factory.lithe` | 97 | 349.1 | 333.2 | 144.8 | 29.3 | 29.7 | 6038 | 6039 | 6214 | +1 |
| `bench/uniswap_v2_pair.lithe` | 529 | 338.6 | 337.1 | 128.2 | 26.0 | 26.2 | 5073 | 5073 | 5201 | 0 |
| `bench/vault.lithe` | 75 | 7.8 | 7.7 | 9.1 | 7.4 | 6.6 | 387 | 387 | 400 | 0 |
| **`bench/` (51)** | | 5308 | 4790 | 2253 | 612 | 615 | 89140 | 89173 | 88902 | +33 |
| **`examples/` (71)** | | 6195 | 5575 | 2581 | 694 | 697 | 85979 | 86113 | 87328 | +134 |
| **all (127)** | | 20409 | 13148 | 6360 | 1995 | 2003 | 252311 | 246539 | 247483 | −5772 |

Release at one thread is **1.55×** faster over the whole set; at 16 threads it is **3.21×**, and the three groups range 2.36–5.84×. Fast is **10.2×** faster at one thread and 10.2× at 16, since one build has nothing to spread. The `bench/` and `examples/` groups are only 1.11× at one thread because most of those files are small enough that startup and the fixed per-build cost dominate; the median `bench/` row is 17.9 → 16.8 ms Release (15.9 at 16 threads) and 8.7 ms Fast. The ladder is where the backend work shows: 3.20× Release at one thread and 12.9× Fast.

### The ladder

| N | lines | base R ms | R ms | R µs/line | F ms | F µs/line | R promote+optimize µs/line | F promote+optimize µs/line |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 439 | 34.5 | 26.8 | 61.1 | 16.5 | 37.6 | 21.9 | 14.3 |
| 32 | 871 | 80.0 | 55.6 | 63.8 | 27.4 | 31.5 | 18.8 | 10.0 |
| 64 | 1735 | 261.6 | 143.5 | 82.7 | 51.3 | 29.5 | 20.2 | 9.1 |
| 128 | 3463 | 1122.9 | 467.3 | 135.0 | 129.0 | 37.3 | 26.0 | 9.7 |
| 256 | 6919 | 7407.3 | 2089.0 | 301.9 | 465.4 | 67.3 | 46.9 | 11.8 |

Per-line `promote`+`optimize` from 439 to 1735 lines is **0.64× Fast and 0.92× Release**, inside 3.5's ≤ 1.5× bar; `baseline.json` is Release-only and its same-ratio figure is **2.79×**. The marginal cost is still not flat above 1735 lines — Fast goes 9.1 → 9.7 → 11.8 µs/line and Release 20.2 → 26.0 → 46.9 — which is the `optimize` residual S50 records rather than a bar this table moves. N = 256 is the one rung whose Release runtime moves by more than 0.1 %: 42 512 → 36 573 bytes, −5 939, or −14 %. That contract is over `SIZE_LIMIT` (24 576) on the baseline and still is here, so both builds run the outline-more fallback, which every mode keeps (`## 1.1`); the search now finds a plan 14 % smaller than it did at `796fdfe`. Fast lands on the same 36 573 bytes because the fallback is not a search step and both modes run it.

### Size, every target, against the §2 budget

| measure | base | Release | Fast |
|---|---:|---:|---:|
| creation + runtime, all 127 targets | 520 077 | 508 495 (−2.23 %) | 510 575 (−1.83 %) |
| creation + runtime, the 122 non-ladder targets | 365 643 | 365 939 (**+0.08 %**) | — |
| creation + runtime, the 19 non-ladder targets whose Release code changes | 162 826 | 163 122 (+0.18 %) | — |
| release runtime, `bench/` only | 89 140 | 89 173 (+0.04 %) | — |

The −2.23 % is the ladder's N = 256 shrinking plus 19 real targets, which move between −150 and +194 bytes; without the ladder the release total is **+0.08 %**, well inside 1 %. Six of the 19 move more than 1 % of their own size — up: `erc6909` +194 bytes (+2.68 %), `examples/stdlib/claims` +194 (+2.70 %, the same contract under one name), `stdlib/token` +81 (+1.43 %), `stdlib/ownable_roles` +28 (+1.26 %); down: `erc4626` −150 (−2.31 %), `examples/raw_codec` −20 (−1.31 %). These are the Release keys `tests/snapshots/bytecode.json` moved for 3.2c and 3.3b(ii), each already justified against the totals in those sections; no later step changed codegen. Release is not byte-identical to the baseline anywhere codegen changed — that is what the rest of this file has recorded since 3.2c — while §2's budget is on totals, and the totals pass with 92 % of the allowance unspent.

### Gas and outcomes, all 45 `bench/run.py` suites

`evm::bench_gas` replays every suite's steps through the in-crate interpreter and reports transaction gas, deploy gas, suite runtime bytes, and each step's status and returndata hash. It runs as `cargo test --release --lib evm::bench_gas::bench_gas -- --exact`, the same command `scripts/bench_compile.py` uses to fill `baseline.json`'s `gas` key, so the base and both new columns are measured the same way. Release and Fast each get a full run. Outcomes: **1 294 ok / 492 revert, 1 786 steps**, and every suite's status vector is identical in all three runs. One suite's returndata hashes differ, `uniswap_v2`, for the reason 1.2 and 3.2c record: the factory creates its pair with `CREATE2` and its runtime is 6 038 → 6 039 bytes, so the pair address and the `DOMAIN_SEPARATOR` that commits to it differ on the 12 steps that read a `CREATE2`-derived address. Status stays `ok` on all 12.

The harness has no Fast gas mode, so the Fast column came from a two-line `LITHE_OPT=fast` switch in `src/evm/mod.rs::compile_file` that selects `Opt::Fast` for the test builds, the same device 1.2 used for its Fast gas run; **that switch is not in the tree**, and both the bytecode snapshot and every other test build the default Release. Reproduce the Release column with `LITHE_BENCH_OUT=/tmp/gas.json cargo test --release --lib evm::bench_gas::bench_gas -- --exact`, and the Fast column by adding those two lines, running `LITHE_BENCH_OUT=… LITHE_OPT=fast cargo test --release …`, then removing them.

| suite | base gas | R gas | F gas | base deploy | R deploy | F deploy | base run | R run | F run | gas Δ R | outcomes |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `codec` | 417713 | 417753 | 419637 | 614569 | 618241 | 625377 | 2596 | 2613 | 2646 | +0.0096 % | 12 ok / 3 revert |
| `counter` | 188814 | 188814 | 188814 | 96234 | 96234 | 96234 | 198 | 198 | 198 | 0 | 6 ok / 1 revert |
| `token` | 372657 | 372657 | 372898 | 130646 | 130646 | 139282 | 357 | 357 | 397 | 0 | 7 ok / 4 revert |
| `traits` | 323801 | 323801 | 323801 | 154360 | 154360 | 154360 | 468 | 468 | 468 | 0 | 5 ok / 7 revert |
| `shapes` | 634279 | 634279 | 634808 | 335825 | 335825 | 343177 | 1306 | 1306 | 1340 | 0 | 5 ok / 20 revert |
| `reasons` | 571023 | 571023 | 571040 | 258073 | 258073 | 258269 | 844 | 844 | 845 | 0 | 6 ok / 15 revert |
| `strings` | 970540 | 970540 | 972130 | 426262 | 426262 | 419989 | 1724 | 1724 | 1695 | 0 | 16 ok / 10 revert |
| `vault` | 317954 | 317954 | 318000 | 137130 | 137130 | 139906 | 387 | 387 | 400 | 0 | 6 ok / 4 revert |
| `selectors` | 267094 | 267094 | 267290 | 139452 | 139452 | 150268 | 399 | 399 | 449 | 0 | 7 ok / 2 revert |
| `logs` | 203290 | 203290 | 203450 | 113044 | 113044 | 119100 | 277 | 277 | 305 | 0 | 6 ok / 0 revert |
| `env` | 116703 | 116703 | 116703 | 70684 | 70684 | 70684 | 81 | 81 | 81 | 0 | 4 ok / 0 revert |
| `date_time` | 396468 | 396468 | 397991 | 305282 | 305282 | 302240 | 1166 | 1166 | 1152 | 0 | 14 ok / 1 revert |
| `math` | 216943 | 216943 | 216943 | 144860 | 144860 | 144860 | 424 | 424 | 424 | 0 | 6 ok / 3 revert |
| `numerics` | 2381064 | 2381064 | 2381862 | 416065 | 416065 | 421041 | 1679 | 1679 | 1702 | 0 | 96 ok / 10 revert |
| `fixed_point` | 1662324 | 1662324 | 1662907 | 664955 | 664955 | 683760 | 2831 | 2831 | 2918 | 0 | 69 ok / 5 revert |
| `layout` | 703234 | 703234 | 703234 | 205473 | 205473 | 205473 | 705 | 705 | 705 | 0 | 20 ok / 1 revert |
| `records` | 1773784 | 1773784 | 1773805 | 379148 | 379148 | 379148 | 1508 | 1508 | 1508 | 0 | 30 ok / 4 revert |
| `lists` | 733731 | 733731 | 734679 | 404327 | 404327 | 398906 | 1624 | 1624 | 1599 | 0 | 17 ok / 5 revert |
| `texts` | 1951926 | 1951926 | 1956723 | 940824 | 940824 | 898785 | 4105 | 4105 | 3911 | 0 | 42 ok / 12 revert |
| `loops` | 614339 | 614339 | 614362 | 241501 | 241501 | 242149 | 871 | 871 | 874 | 0 | 15 ok / 1 revert |
| `names` | 1679284 | 1679284 | 1680607 | 336877 | 336877 | 331907 | 1312 | 1312 | 1289 | 0 | 32 ok / 2 revert |
| `base64` | 420292 | 420292 | 421267 | 245739 | 245739 | 242101 | 891 | 891 | 874 | 0 | 12 ok / 0 revert |
| `overloads` | 403648 | 403648 | 403876 | 152176 | 152176 | 150244 | 458 | 458 | 449 | 0 | 9 ok / 3 revert |
| `tally` | 394299 | 394299 | 394299 | 148090 | 148090 | 148090 | 439 | 439 | 439 | 0 | 8 ok / 2 revert |
| `collections` | 1132123 | 1132123 | 1132177 | 188708 | 188708 | 190654 | 627 | 627 | 636 | 0 | 24 ok / 2 revert |
| `registry` | 1415692 | 1415692 | 1417006 | 306261 | 306261 | 305177 | 1034 | 1034 | 1028 | 0 | 32 ok / 2 revert |
| `relay` | 1124027 | 1124027 | 1126344 | 1401808 | 1401808 | 1347207 | 5991 | 5991 | 5739 | 0 | 7 ok / 1 revert |
| `dial` | 452973 | 452973 | 454587 | 660159 | 660159 | 641325 | 2561 | 2561 | 2474 | 0 | 7 ok / 1 revert |
| `profile` | 439226 | 439226 | 439962 | 756561 | 756561 | 756024 | 1758 | 1758 | 1752 | 0 | 14 ok / 0 revert |
| `erc20` | 1244833 | 1244635 | 1247917 | 647380 | 652719 | 604001 | 2244 | 2269 | 2042 | −0.0159 % | 25 ok / 18 revert |
| `erc721` | 2570130 | 2570138 | 2576092 | 977909 | 979375 | 979717 | 3528 | 3535 | 3534 | +0.0003 % | 41 ok / 25 revert |
| `erc1155` | 4968746 | 4968711 | 4994531 | 1668104 | 1670906 | 1618738 | 6393 | 6406 | 6164 | −0.0007 % | 57 ok / 47 revert |
| `erc6909` | 2486070 | 2485730 | 2491749 | 873118 | 894035 | 862698 | 3326 | 3423 | 3275 | −0.0137 % | 57 ok / 17 revert |
| `erc721_full` | 8299747 | 8300452 | 8309308 | 1555648 | 1552149 | 1566801 | 6094 | 6078 | 6144 | +0.0085 % | 130 ok / 84 revert |
| `erc4626` | 2200528 | 2201577 | 2207220 | 1364952 | 1356702 | 1360398 | 5256 | 5218 | 5233 | +0.0477 % | 54 ok / 8 revert |
| `safe_erc20` | 504262 | 504262 | 506092 | 817898 | 823237 | 774519 | 2787 | 2812 | 2585 | 0 | 10 ok / 2 revert |
| `ownable_roles` | 557293 | 557293 | 557600 | 284784 | 284784 | 289770 | 952 | 952 | 975 | 0 | 14 ok / 4 revert |
| `erc20_full` | 6789562 | 6789846 | 6806198 | 2120779 | 2110414 | 2141006 | 8204 | 8156 | 8297 | +0.0042 % | 106 ok / 42 revert |
| `solady_erc20` | 1371033 | 1371033 | 1371430 | 354803 | 354803 | 356317 | 1395 | 1395 | 1402 | 0 | 33 ok / 12 revert |
| `solady_erc721` | 2304732 | 2304732 | 2306785 | 660714 | 660714 | 673691 | 2564 | 2564 | 2624 | 0 | 36 ok / 21 revert |
| `solady_erc1155` | 3478017 | 3478017 | 3486115 | 1043237 | 1043237 | 1034600 | 4087 | 4087 | 4047 | 0 | 40 ok / 33 revert |
| `deployers` | 1177479 | 1177479 | 1180789 | 474308 | 474308 | 485398 | 1701 | 1701 | 1752 | 0 | 21 ok / 4 revert |
| `swap` | 1006980 | 1006980 | 1007525 | 373267 | 373267 | 382113 | 1224 | 1224 | 1264 | 0 | 10 ok / 6 revert |
| `uniswap_v2` | 5295906 | 5295914 | 5306397 | 2677002 | 2687934 | 2628325 | 10526 | 10577 | 10298 | +0.0002 % | 100 ok / 39 revert, hashes differ |
| `staking` | 1585578 | 1585578 | 1593981 | 2007664 | 2018342 | 1854341 | 6974 | 7024 | 6261 | 0 | 26 ok / 9 revert |
| **45 suites** | **68 120 141** | **68 121 662** | **68 250 931** | **28 276 660** | **28 315 691** | **27 918 170** | **105 876** | **106 059** | **104 194** | **+0.0022 %** | **1 294 ok / 492 revert** |

- **Release transaction gas +0.0022 %** (68 120 141 → 68 121 662), **deploy gas +0.138 %**, **gas including deploy +0.042 %**, **suite runtime bytes +0.173 %**. Everything is inside §2's 1 %. This is the accumulated cost of 3.2c's pair selection and 3.3b(ii)'s batched promotion, which `## 3.2c` and `## 3.3b(ii)` each gate and justify; nothing moved them.
- **Fast is within the same budget and cheaper to deploy in aggregate:** transaction gas **+0.192 %** (68 250 931), deploy gas **−1.268 %** (27 918 170), gas including deploy **−0.236 %**, suite runtime bytes **−1.589 %**. Per suite the sign flips both ways — `erc20_full` costs 0.25 % more per step and 0.95 % more to deploy in Fast, `erc1155` 0.52 % more per step and 2.96 % less to deploy — so the aggregate is the number the §2 budget is on.
- Both modes' step statuses are identical to the baseline in every suite. §2's rule is that an outcome change is a behaviour change; there is none, in either mode, across 1 786 steps.

### Headlines against §4's targets

| target | bar | measured |
|---|---|---|
| `erc20_full` Fast compile | ≤ 60 ms (Phase 1), ≤ 15 ms (Phase 3) | **50.4 ms** at one thread, 50.7 at 16 — Phase 1 met with 16 % margin, Phase 3 **not met** |
| synthetic 1 735-line contract, single build | ≈ 195 ms (prompt's baseline), ≤ 25 ms Phase 3 | **51.3 ms** Fast wall (40.8 backend), 143.5 ms Release. `baseline.json` measured this rung at 261.6 ms so the drop is 5.1× Fast / 1.82× Release; the ≤ 195 ms reading is met, ≤ 25 ms is **not met** |
| LSP diagnostics on an `erc20_full` edit | ≤ 20 ms Phase 2, ≤ 5 ms Phase 3 | 6.3–6.5 ms in release, 7.7–7.9 dev — Phase 2 met, ≤ 5 ms **missed**; the floor is `check` alone at 5.1–7.0 ms (`## 2.6`, `## 5.1c`) |
| Release bytes and gas on `bench/` | identical at Phase 1, within 1 % by Phase 3 | **+0.08 %** bytes without the ladder, **+0.0022 %** transaction gas, outcomes identical |
| Threads | determinism at 1 and N | bytes identical at 1 and 16 on all 127 targets, in both modes |

`erc20_full` in Fast, phase by phase at one thread: check 5.7 ms, backend 35.8, emit 5.5, promote 4.7, optimize 11.6, outline 9.0, body 5.4, 1 emit / 2 finishes, creation 9 380 / runtime 7 426. Release at one thread is 1 438.2 ms (99 emits / 93 finishes) against 1 731.9, and 452.7 ms at 16 threads. Two numbers worth stating plainly: Release is only **1.20×** faster at one thread on this contract, because the search still runs 99 candidate builds and the per-candidate passes are what 3.2c and 3.3b(ii) sped up; and Fast is **34×** faster, which is the whole point of 1.1.

Threads help Release (1 438.2 → 452.7 ms, 3.18×) and do nothing for Fast (50.4 → 50.7, inside noise) because Fast is one build and there is nothing to spread. `gen::budget` is one process-wide pool (S43), so these N-thread rows mean what they say.

### The architecture page against what landed

`docs/src/pages/guide/architecture.mdx` was read line by line against the tree at this commit. Its stages, the block IR, the promotion description and the stack-too-deep argument are what landed. Two sentences did not match and are corrected here:

- **"A block starts at its labels, or right after an instruction that ends execution or jumps away"** said `JUMPI` ends a block. It does not: `is_terminal` is `STOP | JUMP | RETURN | REVERT | INVALID | SELFDESTRUCT` (`src/asm.rs`), and `asm::blocks` keeps a run through a `JUMPI` together on purpose (`## 3.1`). The page now says a conditional jump stays inside the block, and that the marked path runs the passes on the stream so prover marks survive — the `track::on()` branch in `asm::optimize`.
- **"Each candidate is priced with the same gas and byte cost model the rest of the backend uses (`asm::gas`, `byte_gas`)"** was written in `6104ed6` (3.4) about `promote`. `promote` prices bytes: `rest` counts each later load as 2 bytes saved and each store as 1, and `plan_region` adds `saved += 2` per rewritten load and `+= 1` per store, with the `floor` a byte count. There is no call to `asm::gas`, `byte_gas` or `heat` anywhere in `promote`, `plan_promotion`, `promote_region`, `region_batch`, `plan_region` or `hold`, and none in the same region at `796fdfe` either, so the sentence was wrong when written rather than made wrong by a later step. The page now says promotion is priced by the bytes it saves, and keeps the gas-and-byte cost model for the two places that do use it: plan selection in `gen::codegen` (`priced`, `asm::gas`/`gas_from` plus `byte_gas * runtime`) and `outline`'s `gain` (`heat * gas` less `byte_gas * bytes`).

The rest of the page's claims were re-checked rather than assumed: every local has a memory word (`Gen.local: Vec<i32>`, loads `Mem(addr)` + `Op(MLOAD)`); promotion refuses a rewrite beyond reach (`(0..16).contains(&above)` in `hold`, `d < 16` in `plan_region`/`walk_alias`, `d >= 16` refusing in `abandon_walk`); the outliner refuses a run that takes or leaves more than 16 (`takes > 16 || leaves > 16`) or whose parameters sit deeper than 16 (`fetches`). The page needs no other change, and no §5 step is left to land that would move it.

## S28 5.1b + 5.2: scope re-measured, split again

The step asks for one slice that flips `NameAt`/`Expr::{Ident, Field, Call}`/`TypeRef` to `Symbol`, replaces every `origin: String` with a `FileId` and every `line`/`col` with a byte `Span`, and removes four `Program` clones, inside `ast.rs`, `check/mod.rs`, `lib.rs`, `lint.rs`, `parse.rs`. Counted on this tree (`grep -rcE` over `src/`):

| what moves | lines | files |
|---|---:|---:|
| `\bline\b` / `\bcol\b` (spans) | 2 339 / 2 002 | 71 / 53 |
| `.origin` (`FileId`) | 242 | 25 |
| `Expr::Ident` / `Expr::Field` / `Expr::Call` | 281 / 180 / 296 | 44 / 38 / 38 |
| `TypeRef::Name`, `NameAt` | 30, 59 | 13, 9 |

Five of those files are this slice's. The rest are `check/*`, `gen/*`, `prove/*`, `evm/*` (the differential gate's harnesses), `split.rs`, `spec/*`, `modules.rs` and `index.rs`, which sibling steps were editing concurrently. The design for lazy line/col is settled: one `SourceMap` per compilation (`modules::Sources`, or the LSP session), one entry per (path, content hash), and `Error` resolves its `Span` to `line`/`column` at the `modules.rs`/`lib.rs::Error::in_file` boundary. That boundary covers `Error`, but not the places that put a position into text or a non-`Error` value. These need the map passed in: `modules::Site::place` (cross-file "declared at" text inside diagnostics), `check::format_note` and `Note` (warnings), `split::warning`, `prove/exec.rs` (`loop_places`, counterexample notes), `spec/instrument.rs` ("loop invariant at line:col"), `lint.rs`, and the LSP/`index.rs` position lookups.

**Two of the four clones are structural; the other two landed (below).** `Checked.source` is the program before `compose` rewrites it, and `split::facet_program`, `gen`, `index` and `compose`'s ERC-165 re-check all read it, so a snapshot is needed while `check` takes `Program` by value. `spec::check(prog.clone())` in `build` exists because `spec::check` and `check::check` both consume and mutate the program. Neither goes away until `check` borrows the AST, which is 5.5's arena. **(S32 measured this: borrowing cannot remove them, because `Checked.source` is the pre-`compose` program, a different value from `checked.prog`. See `## S32 5.5 closed: not taken`.)**

**What landed (byte-identical, no diagnostic changes):**
- `analyze_in` iterates `&units` and clones each unit once for `check_in`; only a `Full` pass clones it again for `build`. A keystroke (`Pass::Edit`) went from three deep `Program` copies per unit (`units.clone()`, `unit.clone()`, `Checked.source`) to two.
- `lint::units` no longer copies the loaded program to keep a fallback for a broken spec file; it loads the file again on that (error-only) path.

**Split proposed:** 5.2a, a `Span`/`FileId` source map in `ast`/`parse` with `line()`/`col()` accessors and one owner for the call-site sweep; 5.1b, the `Symbol` flip of the four AST shapes, also one owner of `check`/`gen`/`prove`/`evm`; and the `Checked.source` and `spec::check(prog.clone())` clones carried into 5.5 (not closed here): both exist because `check` takes `Program` by value and mutates it, and both go once 5.5's arena lets `check` borrow the AST. **(S32: neither does; see `## S32 5.5 closed: not taken`.)**

## 5.2a

Plan: replace every AST `line`/`col` with a byte `Span` and every `origin: String` with a `FileId`, resolving text positions from one source map. Proof: both bytecode snapshots, the whole suite with an assert that no error reaches `Display` unresolved, and a before/after diff of every diagnostic the CLI prints. Expected: no number moves except, perhaps, the LSP one.

**What changed.**
- `ast`: `Span { lo, hi }` (the bytes of the token a node starts at; `Span::NONE` is the old line 0), `FileId(u32)` (`FileId::NONE` is the old empty origin), and `SourceMap` (path, content hash, line starts; `add` dedupes on (path, hash)). `Program.files: Arc<SourceMap>`, shared by its siblings and peers. `parse::line_starts` builds the table.
- One map per compilation: `parse` gives a lone file its own; `modules::load_in` owns the load's, adds each file as it reads it (cached parses included, since their spans are file-relative), and stamps each declaration's `FileId`; `load_specs` adds spec files.
- `Error` keeps `file`/`line`/`column`/`message` public. Two crate-private fields carry an unresolved span and the `FileId` `in_file` named; `Error::placed(map, own)` writes `line`/`column` (and the path, when `in_file` named one). It runs where errors leave a map's reach: `parse`/`parse_specs`, `load_in`/`load_specs`, `check_in` and `several_contracts`, `compile`'s per-unit build, and the post-check entries `split::build_from`, `gen::entrypoints`, `route::{abi, method_ids, render_errors}`, `spec::{check, instrument}`. A place no `in_file` named is read in the program's own file and gets no path, as before. `in_path` is the old string `in_file` for the call sites that only know a path. External code that built `Error` by literal (`main.rs`, `standard_json.rs`, `lsp.rs`, `playground/`) now clones or calls the new `Error::new(line, column, message)`.
- Text that is not an `Error` resolves through the map where it is made: `modules::Site::place` (holds the map), `check::Note` (resolved where the checker writes it, so `format_note` and `lint` are unchanged), `split::warning` and `split::Site`, `spec/instrument` (`loop invariant at l:c`, `--check-specs` warnings), and the prover. `prove::exec` tracks the file of the code it runs (set per subject, invariant and clause, swapped on calls), a `Stop` from inside a call carries the callee's file, and `bspec::Reader` does the same for `(at l:c)`.
- `lint` keeps its `(line, col)` findings, sort and dedupe unchanged; binds hold spans resolved once against the file's own text, and keyword lookups match on byte offset.
- `split::Site` stays `(path, line, col)` because the facet cache serializes it and `FileId`s are only stable within one load.

**The `index::Span` collision.** `index::Span { file, line, col, len }` (public as `lithe::Span`) keeps its name and meaning: the LSP-facing place, already resolved. The index resolves each AST span to line/column through its own per-file line table (`Builder::lc`, `locate_at`, `offset_at`) when it builds, and refers to the AST type only as `crate::ast::Span`, so the two never meet at the LSP boundary. Storing byte spans in the index would change every LSP path for no measured gain.

**Found on the way.** `gen::calls`' statement-shape key strips positions from the statements' `Debug` text; it matched `line: N, col: M, ` and silently stopped stripping, which changed `bench/safe_erc20.lithe:Payer` and `fuzz/shared_arms.lithe` in both snapshots until it matched `span: Span { .. }, ` instead. `SourceFile`'s `Debug` prints only path and content hash, because facet memo and cache keys hash `Program`'s `Debug`.

**Gates.**

| gate | result |
|---|---|
| `evm::snapshot` (Release and Fast, with and without VERIFY) | unchanged |
| `cargo test --locked`, with a temporary `assert!` in `Error`'s `Display` that the span was resolved | 562 lib + 25 bin + 1 pass, no unresolved error displayed |
| diagnostic corpus: `compile`, `abi`, `errors`, `specs`, `lint` over `examples/`, `bench/`, `fuzz/`, `std/`, plus 797 variants (lines 3/7/13/21/34/55/89 deleted, junk appended) | 7 342 lines, `cmp` identical between `b1c574a` and this tree (1 937 positioned lines, 866 warnings) |
| `make check` (fmt, clippy, test, VERIFY test, differential at 2 000 steps, snapshot, bench-gas, wasm playground) | green, exit 0 |

**Number.** `lsp::tests::did_change_coalesces_and_erc20_full_diagnostics_are_fast` (20 ms limit), release, best of 5 per run, three runs each: before (`b1c574a`) 6.87 / 6.54 / 6.28 ms, after 6.23 / 6.24 / 6.26 ms. That is within run-to-run noise: the sweep does not move it. The test now prints the number under `--nocapture`. Spans are the same size as the pairs they replace, and the only frontend allocation removed is one `String` per declaration (`origin`), which is not where `check`'s 5–7 ms goes. The ≤ 5 ms target stays with 5.1b/5.1c (names); 5.5 (the arena) was measured in S32 and does not move it.

**Known edge, not reached by any test or the corpus.** An error raised after `check` from a span inside an imported module's function, with no `in_file` on its way out, used to print that module's line and column under the contract's name. It now reads the contract's own line table, because nothing on that path says which file the span is in. Every such site the corpus and suite reach either names its file or is in the contract's file.


## 5.1b

Plan: flip `NameAt.name`, `Expr::Ident`, `Expr::Field`, `Expr::Call` and `TypeRef::Name` from `String` to `Symbol` in one pass, reading every diagnostic string and every order-sensitive site through the interner, so output text and bytecode stay identical. Proof: both snapshots unchanged, the whole suite and VERIFY green, the differential gate at 2 000 steps, and a byte-diff of every diagnostic the CLI prints against the parent commit. Expected: bytecode and text unchanged; `check` is the number to record for 5.1c.

**What changed (36 files, one shape).**
- `Symbol`: `Copy`, `Ord`, `Hash`, and read through `Names`: `as_str` (the text), `Display`/`Debug` (the text, never the number), `PartialEq<str|&str|String>` both ways so `name == "length"` and `name.as_str()` both work, and `is_empty`/`empty` for the "no name of its own" sentinel that was `String::new()`. The stored texts are `&'static str` (`Box::leak` per distinct text, which the table never frees), so reading a name allocates nothing.
- Interning happens once, in `Parser::ident`/`sym`/`name_at`, plus `path_expr`, `call`, and the spec-form builders. `parse` still returns `String` from `ident` for the declaration fields that stay `String` (`Func.name`, `Decl.name`, `Raised.name`, …) — only the five fields the step names moved.
- `Names::Debug` is `Names(..)`. `Program`/`Stmt`/`Expr` `Debug` text is a cache key (`split`'s facet memo, `cache_key`) and the statement shape `gen::calls` compares, so printing the table would both recurse into the same mutex (`Symbol`'s `Debug` reads it) and put interning order into the key.
- **Order-sensitive sites read text.** `modules::imply` sorts the composed modules by name, so its `min_by` compares `Names::get` text, not symbol ids (ids depend on intern order; text order does not). Every other sort in the crate sorts `String` keys that never moved.
- `resolve` keeps its own tables (`Scope.names`, `decls`, …) as `String`, and reads a symbol's text in and interns the rewritten text out through `named_sym`/`module_ref_sym`, so canonical-name rewriting is unchanged. `check` likewise keeps its `String` maps: `Checked.named`, `domain_tys`, scopes. Those are 5.1c.

**Found and fixed on the way.**
- The `Debug`-as-cache-key design deadlocked `cargo test` at `asm::tests::incremental_analyses`: `Inner`'s derived `Debug` formatted `Symbol`s, whose `Debug` re-locked the same mutex. Making `Names::Debug` opaque fixed it; the backtrace is in the transcript.
- `pick_overload` renames the call in place (`credit` → `credit@1`), so the checker must re-read the name after it returns. The first version captured the text before, and `examples/overloads.lithe` failed with `unknown function 'credit@1'`.

**Gates.**

| gate | result |
|---|---|
| `evm::snapshot` (Release and Fast, with and without VERIFY) | unchanged |
| `cargo test --locked` | 564 lib + 25 bin + 1 doctest, 0 failed (566 with the two regression tests below) |
| `LITHE_VERIFY=1 cargo test --locked --lib` | 564 passed, 0 failed |
| `LITHE_FUZZ_STEPS=2000` differential | 5 passed |
| `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check` | clean |
| diagnostic corpus: `compile`, `abi`, `errors`, `specs`, `lint` over `examples/`, `bench/`, `fuzz/` | 36 369 lines, `cmp` identical to `411bf45` |

**Two review findings, both real, both fixed.**
- `Expr::Call`'s module qualification read a `spelled` captured before `pick_overload` and before the alias block, which can rename the call (`A.f`, or a hook's `M.f#hook`) and clear its base. The parent read `name` at that point; the flip captured it early, so a module that calls `A.f` while declaring its own hook `f` was retargeted to its own hook — different code. The block now reads `name.as_str()` inside, as the parent read `name`. Test `evm::hooks::a_qualified_call_is_not_the_callers_own_hook` fails on the pre-fix tree with `3` (M's hook) where the answer is `7` (`A.f`).
- `zero_value`'s `TyKind::Option` case synthesized `name: Symbol::empty()` where the parent wrote `"None"`. That is a value, not a field type: `contextual` tests `name == "None"`, `index.rs` attaches the `None` hover and reference off the text, and `route::fmt_expr` prints it. Restored to `Names::shared().intern("None")`. Test `evm::storage::delete_of_an_option_names_none` fails on the pre-fix tree with `name: ""`.
- Neither changed the snapshots or the corpus, which is why the S58 gates above did not catch them; the differential gate does not exercise a module that requires another while declaring a hook of the same name. Both new tests are in the suite the gates now run.

**Number (`check`, the one 5.1c is measured against).** `bench/erc20_full.lithe`, `--release`, `LITHE_CACHE_DIR=` (cache off), min of 25, load 1–2: parent `411bf45` **5.05 ms** → this tree **5.90 ms**. Re-measured after the two fixes below: 5.82–6.09 ms (min of 15, load 1.5), unchanged. Interleaved A/B on one box: 5.02/5.35 median → 5.89/6.07 median, so about +0.9 ms over the 5.3–5.8 ms S57 recorded for `check`. That is the price of a table lookup where an inline `String` was: `erc20_full` makes **138 263** `as_str` calls per compile (counted with a temporary atomic), and each is a lock plus an index. Three read paths were measured and all landed within noise of each other — `Mutex<Vec>`, `RwLock<Vec>`, and fixed `OnceLock` chunks — so the cost is the lookup itself, not the lock. Removing the per-read `Arc::clone` (a `&'static Names`) and the per-identifier `to_string` in `check/place.rs`/`check/expr.rs` cut the gap from 1.8 ms to 0.9 ms. **This is the number 5.1c is measured against**, and it is expected to invert: 5.1c replaces `Checked.named`, `domain_tys` and the scope maps with symbol keys so `check` stops hashing strings at all, which is the win the 5.1a record predicted would not come from the AST fields alone.

## 5.1c

Plan: `Checked.named` and `domain_tys` become `FxHashMap<Symbol, usize>`, and so do the checker's own scope maps (`Scope.vars`, plus the new `lookup`/`define`/`resolve` on `Symbol`). `route.rs::InternalNames` and `index.rs` are the only two places that iterate a name map in an order the output shows, so both sort on `Names::get` text rather than on the symbol id, whose order is the interning order. Proof: both snapshots unchanged, the whole suite and VERIFY green, the differential gate at 2 000 steps, a diagnostic corpus byte-diff against the parent, and `check` measured before and after. Number to move: the **5.83 ms** min S58 recorded for `check` on `erc20_full` (Release, cache off).

**What moved.**
- `Checker.named`, `Checker.domain_tys` and `Scope.vars` are `FxHashMap<Symbol, usize>`. `Checked.named`/`Checked.domain_tys` too, so the ABI and the index read the same keys the checker wrote.
- One helper, `ast::intern(text) -> Symbol`, reads the process-wide table by reference (`Names::global()`) instead of taking an `Arc` per identifier. `define_str`/`resolve_str` are the same for the callers whose name is still a `String` (a module parameter, an assignment path), so no call site had to change type.
- **The two order-sensitive sites sort on text.** `route::InternalNames::new` used to `sort()` `(&String, &usize)` pairs, which is `String` order; it now sorts `.iter()` on `name.as_str()`. `index.rs`'s `type_names` table took the first name in hash order and used to sort by `(len, text)`; it now sorts by the same key read through `as_str()`. Both produce the same order as the parent, so ABI `internalType` strings and hover type names are unchanged — the corpus below checks that.
- `type_name` no longer uses `.find()` on a hash-ordered iterator (which picked an arbitrary one of a type's names); it picks the alphabetically smallest text. That is deterministic where the parent was not, and no corpus diagnostic moved (finding below).

**Gates** (all on this tree, `f0c8781` + the review fixes; `make check` end to end exited 0):

| gate | result |
|---|---|
| `evm::snapshot` (Release and Fast, with and without VERIFY) | unchanged |
| `cargo test --locked` | 564 lib + 25 bin + 1 doctest, 0 failed (2 ignored) |
| `LITHE_VERIFY=1 cargo test --locked` | 564 lib + 25 bin + 1 doctest passed, 0 failed |
| `LITHE_FUZZ_STEPS=2000` differential | 5 passed |
| `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check` (crate and playground) | clean |
| playground wasm build | green |
| diagnostic corpus: `compile`, `abi`, `errors`, `specs`, `lint` over 245 `examples/`, `bench/`, `fuzz/` files (1 225 invocations) | 52 213 lines, `cmp` identical between `c11cee2` and this tree |

**Number (`check`).** `bench/erc20_full.lithe`, `--release`, `LITHE_CACHE_DIR=` (cache off), interleaved A/B on one box, 25 runs each, min: parent `c11cee2` **5.83 ms** → this tree **5.67 ms** (medians 6.20 → 5.98). That inverts about half of the 0.9 ms S58 paid for the AST flip, not all of it: the scope maps are reached on every name the checker resolves, but the AST flip also made every *diagnostic* and every `Debug` cache key read a name through the table, and those reads stay. The rest of the gap is not more interning; 5.5 (the `Program` clones) was measured in S32 at 3 clones and 0.8–0.9 ms per build, and 5.6 (the module cache) landed with no resolvable change.

**Review findings.**
- **`make check` red** (high): `cargo fmt --check` failed at five sites and clippy failed on `intern(&iface)` where `iface: &str`. `cargo fmt` run; the call is `intern(iface)`. Both now clean.
- **No measurement recorded** (medium): this record and the numbers above are the answer.
- **`type_name` order change** (low): `.min()` on text instead of `.find()` on hash order. Deliberate: the parent's pick depended on interning order, which 5.1a's determinism test exists to forbid. Where a type has more than one name (two aliases of one map/list, a generic instantiation) the printed name is now the alphabetically first, and the 52 213-line corpus — which includes the alias and generic targets — is byte-identical to the parent, so no diagnostic in it reaches that difference.
- **Files outside the owned set, and interner growth** (info): the signature changes to `lookup`/`define`/`resolve` force edits in `ast.rs` and `check/{builtins,expr,funcs,generic,place,spec_forms,stmt,types}.rs`; they are mechanical call-site changes, no logic. `define_str`/`resolve_str`/`intern(..)` do intern text the process never frees, which matters only for a long LSP session and is small (one entry per distinct identifier text, not per use). The table's lifetime is 5.1a's design, not this step's; a session-scoped table is the upgrade path if it ever matters.

## 5.6

Plan: thread one `ModuleCache` through `compile_dir`/`abi_dir` so the 51 files of `bench/` share parsed imports instead of each re-parsing `lib/`. Proof: the output tree byte-identical to the parent's, 1-thread and 8-thread trees identical, snapshots unchanged. Number to move: `lithe abi bench` at one thread, and `lithe compile --fast bench`.

**What landed.** `emit_dir` makes one `ModuleCache` and passes it down through `emit_file` to `compile_cached` → `modules::load_cached`. `compile` is now `compile_cached(.., None)`, so every other caller is untouched. One new test, `modules::tests::files_of_one_directory_build_share_a_parsed_import`, asserts that two entry files importing the same `lib/` file leave three parsed programs in the cache, not four; it fails if the cache is dropped on the floor.

**What the cache already covered, and what it did not.** `ModuleCache` keys parsed programs on `(path, content hash, EVM tag)` and `Checked` on `(path, fingerprint)` — `lib.rs`'s `analyze_in` has passed one since Phase 2. What was missing was that `compile_dir` passed `None`, so *directory mode* re-parsed each importer's imports. `std/` was already process-cached separately (`std_programs`), so the redundant work was the non-`std` files: over the 51 bench entries, 111 parse attempts for 68 distinct files — 43 re-parses, 41 of them the 17 `bench/lib/` files (1 705 lines, each imported 2–7 times) and 2 the factory's import of `uniswap_v2_pair`.

**Why the number does not move.** Measured on `bench/` (51 entries, 68 loads including imports), `LITHE_THREADS=1`, `LITHE_CACHE_DIR=`:

| phase | total | share of the 360 ms build |
|---|---|---|
| `modules::load` (canonicalize, read, parse, link, merge) | 20.3 ms | 5.6 % |
| every `parse::parse`, all 306 attempts including `std/` | 8.0 ms | 2.2 % |
| the 111 non-`std` attempts for 68 distinct files | 5.3 ms | 1.5 % |
| the 43 redundant attempts this change removes | 2.2 ms | 0.6 % |
| the 43 cache hits, each a `Program` clone | 0.48 ms | 0.13 % |

So the whole of parse reuse is about **1.7 ms of 360 ms (0.5 %)** net, below this box's run-to-run spread at that granularity. The remaining ~300 ms is `check` 19.7 ms plus `gen`/backend 298 ms, which is Phase 1/3's, not this step's. Wall clock, interleaved A/B, 5 runs each, `LITHE_CACHE_DIR=` (build cache off), one thread:

| command | parent `6ae833d` | this tree |
|---|---|---|
| `lithe abi bench` | 0.36–0.37 s | 0.35–0.37 s |
| `lithe compile --fast bench` | 0.35–0.37 s | 0.37 s |
| `lithe compile --release bench` | 4.86–4.90 s | 4.88–4.91 s |

No resolvable change in any of the three, and the record says so rather than claiming one. Both directory modes pay it: the number the step names (`lithe compile bench/`) is the Release row.

**The checked half has no directory-mode consumer.** `check::check` runs per entry on the merged `Program` of that entry — its own contract plus every file it imports flattened into it. Two entry files produce different merged programs, so no entry file can reuse another's `Checked`; there is nothing to share. The memo in `ModuleCache::with_checked` pays where the *same* file is checked twice, which is the LSP's `analyze_frontend`/`analyze_full` on an edit, and it is already wired there (`analyze_in`, `lib.rs:629`). Adding a directory path for it would be dead code.

**Gates.**

| gate | result |
|---|---|
| `cargo test --profile fast` | 565 lib (2 ignored) + 25 bin + 1 doctest, 0 failed |
| `evm::snapshot` (Release and Fast) | unchanged, 2 passed |
| `LITHE_CACHE_DIR= evm::differential` | 5 passed |
| `cargo clippy --profile fast --all-targets`, `cargo fmt --check` | clean |
| `compile --release --fast bench` output vs parent `6ae833d` | `diff -r` identical |
| same, `LITHE_THREADS=1` vs `8` | `diff -r` identical |

**Review findings.** None; this is the first pass.

**What this leaves open.** 5.6's premise was that the module cache was unshared and worth building; the tree says the sharing was three lines of plumbing and the win is 0.6 %. The parsed cache and the checked memo are `std::HashMap` under a `Mutex` with `DefaultHasher`, so a directory build on many threads contends on one lock per lookup — not measured here because `load` is 20 ms of 360 ms total and would need a bigger denominator to show. If directory mode ever gets a frontend-only path where load dominates (a `lithe check` command, or the LSP linting a workspace), 5.4's `FxHash` applies to these two maps first.

## S32 5.5 closed: not taken

**The step asks for two things, and the tree says neither pays.** `Vec<Expr>` + `ExprId(u32)`, with `Func.stmts`/`tail` borrowing from it; and, as a consequence, `Checked.source` and `spec::check(prog.clone())` removed. Both were measured against this tree before any code was written, because the second half is only worth having if the first is.

**1. The flip is a whole-crate rewrite: 1 378 errors in 41 files.** Measured by making exactly the step's change — `Box<Expr>` → `ExprId` and `Vec<Expr>` → `Vec<ExprId>` in `ast::Expr`'s children, plus an `ExprId`/`ExprArena` pair — and asking the compiler (`cargo check --profile fast --lib`). Error classes: 1 019 `E0308` (a `&Expr` where an `ExprId` is wanted), 259 `E0599` (no method on the index), 62 `E0614` (deref of a `Copy`), 22 `E0631`, 10 `E0282`, 5 `E0277`, 1 `E0271`. Distribution, largest first:

| file | errors |
|---|---:|
| `src/gen/expr.rs` | 154 |
| `src/check/expr.rs` | 122 |
| `src/gen/range.rs` | 114 |
| `src/gen/stmt.rs` | 82 |
| `src/route.rs`, `src/gen/storage.rs` | 80 each |
| `src/gen/calls.rs` | 58 |
| `src/resolve.rs` | 56 |
| `src/gen/tree.rs` | 54 |
| `src/gen/list.rs` | 43 |
| `src/gen/plan.rs` | 42 |
| `src/check/mod.rs` | 38 |
| `src/check/stmt.rs` | 37 |
| `src/index.rs`, `src/check/consts.rs` | 34 each |
| `src/gen/decode.rs` | 33 |
| `src/prove/bspec.rs` | 30 |
| `src/prove/exec.rs` | 28 |
| `src/spec/instrument.rs` | 25 |
| `src/parse.rs`, `src/check/place.rs` | 22 each |
| `src/check/generic.rs`, `src/check/funcs.rs` | 18 each |
| `src/spec/mod.rs`, `src/gen/body.rs` | 17 each |
| `src/prove/bytecode.rs`, `src/ast.rs` | 16 each |
| `src/lint.rs`, `src/check/hooks.rs` | 15 each |
| 12 more files | 1–11 each |

The 29 named files add to 1 320 (a two-file row counts both files) and the other 12 to 58, so the 41 files total 1 378.

This is the 184-site shape of 5.1b again, seven times over, and unlike 5.1b it cannot be done incrementally: an `Expr` either holds its children by value or by index. 367 of the crate's function parameters are `&Expr` and 32 are `&mut Expr`; every one of them either becomes `ExprId` plus a `&ExprArena` thread, or keeps taking `&Expr` and forces the arena to hand out borrows that the caller then cannot mutate. `check` mutates expressions in place in 11 whole-node rewrites (`*e = ...`, 8 in `check/expr.rs`) and 100 field writes over eight fields (`*ty`, `*sym`, `*root`, `*leaf`, `*callee`, `*builtin`, `*iface`, `*method`), so the arena's `get_mut` is on the hot path of every one of those, and any `&ExprArena` held across them is a borrow conflict. That is a crate-wide slice in its own right, not a frontend-hygiene step.

**2. The payoff is 3 clones per build, ~0.6–0.9 ms in Fast and ~0.4 ms in Release, and the arena does not make them cheaper.** Instrumented `impl Clone for Program` (size and duration per clone, plus the total) over a whole `erc20_full` build, `target/fast`, `LITHE_THREADS=1`, cache off:

| | Fast | Release |
|---|---:|---:|
| wall time | 53–54 ms | 478–488 ms |
| `Program` clones in a build | 3 | 3 |
| their total cost | 628–905 µs | 392–393 µs |
| share of the build | **1.2–1.7 %** | **0.08 %** |

Per clone, in call order, all three of the *pre-`compose`* program (119–120 functions each): 121 µs, then 256 µs, then 251 µs. The later two are the same value cloned twice by the ERC-165 re-check and cost about twice the first because the allocator's free lists are colder there, which is why the total is 0.6–0.9 ms rather than 3 × 0.15 ms. The share varies with the run because a 53 ms total makes the same absolute cost a different fraction; Release, 9× longer, puts it at 0.08 % consistently. Traced with a backtrace, the three are `check_program`'s own `let source = prog.clone()` and the two inside `compose::supports_interface`'s ERC-165 re-check (`src/check/compose.rs:779`, cloning `checked.source`, then re-checking, then re-checking again). `spec::check(prog.clone())` in `build` adds a fourth and fifth: it runs under `--check-specs` (which only `lithe prove` sets) **or** when the file itself holds spec blocks (`spec::has_specs`, `src/spec/mod.rs:109`), so `bench/`'s 51 entries — none of which carries a spec block, they live in `.spec.lithe` files loaded by a separate path — pay 3 clones each, as measured. On `examples/verification/capped_token.lithe`, which has one, `--check-specs` takes the build to 5 clones and 221 µs of 18.6 ms (**1.19 %**), against 1 clone and 41 µs of 20.3 ms (**0.20 %**) with it off.

**The arena would not cut that cost, because the expressions are not where it goes.** What a `Program` clone costs depends on which program it is, so both are measured, 200 iterations each, `target/fast`:

| program | funcs (own + in modules) | clone |
|---|---:|---:|
| as `modules::load` returns it — what the build's 3 clones copy | 119–120 | 147–160 µs |
| as `checked.prog` (after `compose` inlined every module) | 264 | **298 µs** |

Within the loaded program, the split is not the expressions:

| part | µs |
|---|---:|
| whole program | 141–157 |
| its `Func` bodies (`stmts`+`tail`) | 4 |
| its `modules` | 118–129 |
| other decls | 5 |

A flat `Vec<Expr>` arena cloned on its own, i.e. the best case the step's representation can reach:

| target | tree `Program` clone | flat arena clone |
|---|---:|---:|
| erc20_full | 141.8 µs | **159.5 µs** |
| uniswap_v2_pair | 48.7 µs | 40.2 µs |

erc20_full gets *worse* and uniswap_v2_pair saves 8.5 µs, because `Vec<Expr>` is a flat memcpy of 2 098 nodes where the tree is 2 098 small allocations that mostly fit the allocator's fast path, and erc20_full's cost is its ~120 µs of `Program.modules` — every module's `Func`s, types, errors, events and domains, cloned whether the expressions are boxed or indexed. So the representation change buys nothing even on the number it was chosen for.

**3. `Checked.source` is not an ownership artefact, so borrowing cannot remove it.** The plan's premise is that `Checked.source` exists only because `check` takes `Program` by value. It does not. `check_program` (`src/check/mod.rs:541`) clones *before* `compose`, and `compose` then rewrites the program: it moves every used module's types, errors, error sets, events and functions into the contract's own lists, qualifies their names (`M.twice`), and turns a module's externals into entries (`src/check/compose.rs:239–330`). `Checked.source` is therefore the program **before composition** and `Checked.prog` the program **after** it — different values, not one value stored twice. Measured on a contract that uses a module:

```
module M is { function twice(const x : uint) : uint is x * 2 }
use M;
external function go(const x : uint) : uint is M.twice(x)
```

`checked.source.funcs` is `["go"]`; `checked.prog.funcs` is `["go", "M.twice"]`. And `checked.source`'s own `Debug` text differs from `checked.prog`'s on all four bench targets tried. The readers confirm they want the *pre-composition* program: `split::facet` builds a facet from `checked.source` so a module's facet is the module alone, not the contract with it inlined (`src/split.rs:598`); `split::cache_key` keys on it so two contracts that compose the same module at different sites share one facet (`:1397`); `index::template` looks a `storage`-parameter function up in it because the checker specialized the copy in `prog` (`src/index.rs:557`). A borrow of the AST could not supply any of them: the AST the checker was handed has been composed, and the pre-composition one no longer exists. Keeping it is a snapshot of an intermediate value, which is what `Checked.source` already is.

`spec::check(prog.clone())` is the same story one level up: `spec::check` sets `proving`, attaches module specs and *adds functions* for each clause (`src/spec/mod.rs:167–200`), so it needs its own copy of the program, and `build` then needs the unmodified one back for `spec::instrument` and `check::check`. Borrowing does not help; something has to hold the two.

**4. `Program`'s `Debug` is a cache key, which the arena would put at risk for no gain.** `split::cache_key` and `split::facet` key their on-disk and in-process memos on `format!("{checked.source:?}")`, and `Program`'s `Debug` is documented as a cache key. A `Vec<Expr>` arena makes `Debug` print an index unless the arena is printed too, and printing it in node order is the same text at the same cost; printing it in arena order changes the key. The measured cost of the key is 749 µs per `format!` on erc20_full (518 573 bytes of text) and 1.60 ms with the `keccak256` — 4.8× and 10× the 147–160 µs clone the arena is meant to replace. So the tree representation is not the problem here either.

**What would actually remove the clones, if that were worth doing.** Not the arena: the three sites are `check_program`'s snapshot, which must be a snapshot (above), and `compose::supports_interface`'s re-check, which re-runs `check` on a program with one generated function added — that one could take `&Program` and build only the added `Func`, but `check` needs `&mut` throughout, so it is a `check`-signature change, and it is 2 of the 3 clones. Deleting the `spec` path's clones means `spec::check` stops adding functions to the program it was given, which is a spec-tool redesign.

**Conclusion.** §2's rules make this a failed iteration if landed and a measured close if not. The step is closed as **not taken**: 1 378 errors in 41 files for 0.08 % of a Release build and 1.2–1.7 % of a Fast one, with the specific representation it prescribes measured at *worse* than the tree on the largest target, and its second half (removing `Checked.source`) resting on a premise the tree disproves. Nothing in codegen, diagnostics or the checker changed, so both bytecode snapshots and the diagnostic corpus are untouched by definition, and the tree is green: `cargo test --locked --lib` 565 passed, 2 ignored, 0 failed.

**How the numbers were taken, and their gates.** Every figure above comes from a copy of this tree outside it (`/tmp`), because the instrument is an `impl Clone for Program` that prints and a test that drives a build; nothing of that is in the committed tree. Reproduce with: apply `#[derive(Debug)] struct Program` plus a hand-written `Clone` that times itself, then `cargo check --profile fast --lib` for the error counts, and a `#[cfg(test)]` test loading `bench/erc20_full.lithe` through `modules::load` and `check::check` for the timings. The flat-arena comparison clones a `Vec<Expr>` built by walking the same target's expressions. Since no production code changed, the only gates this step can fail are the ones it does not touch, and they pass on the committed tree:

| gate | result |
|---|---|
| `cargo test --locked --lib` | 565 passed, 2 ignored, 0 failed |
| `cargo clippy --profile fast --all-targets -- -D warnings` | clean |
| `cargo fmt --check` | clean |
| `git status` | only `PROGRESS.md` modified |

**What would reopen it.** A measured frontend bottleneck where expressions dominate a clone or a `Debug` key: `check` on a contract an order of magnitude larger than any in `bench/`, where the 2 098 expressions become ~20 000 and `Program.clone` becomes the difference between 12 ms and 5 ms of LSP latency. §4's 5 ms LSP target is currently `check` at 5.1–7.0 ms (`## 2.6`), and the clones are 0.4–0.9 ms of a 54 ms Fast build, so they are not that bottleneck on today's targets. If a later slice makes `check` cheap enough for the clones to become the floor, the cheaper fix is `compose::supports_interface`'s two clones, not the AST's representation.

## S30 5.7

Two halves: identifier slices + interning in the lexer path, and statement-level parser recovery that reports all errors with the first unchanged.

### The lexer half was already done, and the waste was one level up

The step prescribes "stop materializing `String` token payloads for identifiers (slice + intern)". The lexer already does not: `Token` (`src/lex.rs:570`) is `{kind, start, end, word, string}`, and `string` is set only by `Raw::Number(Num::Bytes)` and `Raw::String` — never by `Raw::Ident`. Identifiers are a byte range, and the parser slices `src[start..end]`. So there was no `String` payload to delete.

The `String` that was being materialized is in the **parser**:

```rust
fn ident(&mut self) -> Result<String, Error> {
    let name = self.lexeme().to_string();
    self.names.intern(&name);          // intern #1, result discarded
    self.bump();
    Ok(name)
}
```

and then every expression, type and name site interned the same text a second time: `name: self.sym(&name)` in `Expr::Ident`/`Expr::Field`/`Expr::Call`/`TypeRef::Name`, `self.name_at(span, &self.dotted()?)` (which also allocates a `String` and splits/joins it), `path_expr` interning a `Vec<String>` the caller had just built from interned pieces.

The fix is `ident_sym()` (intern once, return `Symbol`) with `ident()` kept as `ident_sym()?.to_string()` for the declaration fields that genuinely hold a `String` (`TypeDecl.name`, `Func.name`, `ModuleDecl.name`, …) — those are 5.1b/5.1c's territory, not this slice's. `member_name_sym`, `dotted_at`, and `named_at` are the symbol forms of the three helpers that allocated; the `Expr`/`TypeRef`/`Stmt::Call`/`delete` sites now use them.

**Measurement (intern calls, `Names::intern` instrumented with an atomic, counted per compile with `--profile fast`, `LITHE_CACHE_DIR=`):**

| contract | before | after | change |
|---|---|---|---|
| `bench/erc20_full.lithe` | 34 940 | 23 833 | −31.8 % |
| `bench/uniswap_v2_pair.lithe` | 24 293 | 14 986 | −38.3 % |
| `bench/erc1155.lithe` | 24 276 | 15 220 | −37.3 % |

**The number this does not move, and why.** `parse` on `bench/erc20_full.lithe` is **0.14–0.16 ms** of which `lex` is 0.035–0.043 ms (probe in a scratch test, `cargo test --release`, 3 runs after warmup; 999 tokens, 365 of them identifiers). The frontend is 6.2 ms, and `check` is 5.7 of it (`[time] frontend load=0.9ms check=5.7ms lint=0.4ms`). The LSP diagnostics test is **6.97 ms before, 6.91 ms after** (best of 5, release) — noise. So this half is hygiene, as §5 predicted ("a feature gap, not a speed item"), and it is recorded as such rather than claimed as a win.

### Statement-level recovery

`block()` no longer propagates a statement's error out of the parse. It records the error and skips to the next `;` or `}` outside brackets (`skip_stmt`), then parses on, so every statement of every block is attempted. A declaration-level error still ends the parse, as before — that is not statement-level, and recovering from it would mean guessing where the next declaration starts.

`Error` carries the rest: `pub(crate) more: Vec<Error>`, exposed as `Error::chain()`. `parse` assembles it:

- the first error is `errors[0]`, which is the earliest error in the file because a block's statements are parsed in order and a declaration error can only follow a complete block;
- the error that ends the parse is pushed **last**, so it never becomes the first error;
- `placed`/`in_path`/`in_file` run over the chain, so every recovered error gets its file, line and column from the same `SourceMap`.

Because the first error is unchanged, every existing caller keeps its behaviour: `compile`, `abi`, `analyze`, `lint` and the LSP all still see the same `Error` they saw before, and the extra ones are only visible to a caller that asks for them.

**Who asks for them.** Two places, and they are the point of the step: `main.rs::fail` prints `err.chain()` (every command that reports a diagnostic), and `lsp.rs::publish` turns every error of the chain into its own diagnostic, so an editor underlines every broken statement instead of only the first.

### Proof it changes nothing that was observable

| gate | result |
|---|---|
| diagnostic corpus: `abi` + `compile --release` over `bench/`+`examples/`+`fuzz/`+`std/`, parent `897f81f` vs this tree, stdout+stderr+exit code | **27 892 lines, `diff` empty** |
| spec-file corpus (**review fix**): `abi` + `compile` + `specs` over every `*.lithe` in `bench/`+`examples/`+`fuzz/`+`std/` (a `specs` run wherever a `.spec.lithe` sits beside it), parent `897f81f` vs fixed | **38 385 lines, `diff` empty** |
| spec-block fuzz (**review fix**): 600 mutated inputs whose statements are real statements from `examples/`, placed inside a spec clause's `then { … }` block (where `spec_file` reaches `block()`), parent `897f81f` vs fixed | **600/600 same first error and exit code**; also **31/300** earlier inputs that the recovery-only tree *accepted* are rejected again, matching the parent |
| `skip_stmt` rewind: every `examples/reject/*.lithe` and the whole corpus above, parent vs fixed | **diff empty**; without the rewind `event_indexed_emit.lithe` gained a spurious ``expected a declaration, found `}` `` (see below) |
| fuzz: 620 mutated inputs (random deletions, insertions from a token list including `.`/`A.`/`A.B.`/`interface I is {`/`supports A`/`spec for f is {`/`raises A.`, truncations) over `bench/`+`examples/`+`std/`, parent binary vs this tree | **0 mismatches** in the first error and the exit code |
| `cargo test --locked` | 569 + 27 + 1 passed, 2 ignored, 0 failed |
| `cargo test --profile fast --locked --lib evm::snapshot` | 2 passed — both bytecode snapshots unchanged |
| `LITHE_FUZZ_STEPS=2000 … evm::differential` | 5 passed |
| `LITHE_VERIFY=1 cargo test --locked --lib` | 569 passed, 2 ignored, 0 failed |
| `cargo clippy --all-targets -- -D warnings` | clean |
| `cargo fmt --check` (crate and `playground`) | clean |
| `playground` `cargo build --release --locked` (wasm) | builds |
| LSP diagnostics, `did_change_coalesces_and_erc20_full_diagnostics_are_fast` | 6.97 → 6.91 ms, limit 20 ms |

The corpus is the strongest evidence here because it is the one the change could break: recovery changes *how many* errors a bad file produces, and it produces **exactly one** on every file in the repo, broken or not. That is what "first error unchanged" has to mean in practice.

**Where recovery is visible, and that the first error is identical** (`/tmp` scratch files, parent binary vs this tree):

```
$ lithe abi bad2.lithe        # parent
bad2.lithe:5:8: expected an expression, found `;`

$ lithe abi bad2.lithe        # this tree
bad2.lithe:5:8: expected an expression, found `;`

bad2.lithe:6:19: expected an expression, found `;`

bad2.lithe:8:10: expected an expression, found `;`

bad2.lithe:9:24: expected an expression, found `;`
```

The nested case (lines 8 and 9 are inside an `if` block) is why `block()` is the recovery point rather than the function body: each nesting level recovers its own statements.

### Tests added (`src/parse.rs`)

- `statement_errors_are_all_reported_in_file_order` — three broken statements, one of them nested, come back in file order with their exact messages.
- `one_broken_statement_is_one_error` — the case the corpus covers programmatically: one broken statement is still exactly one error, at the line it always was.
- `statement_errors_inside_a_spec_block_are_reported` — `spec_file` finishes through `all_errors()` too, so a broken statement inside an `ensures if … then { … }` block rejects the spec file instead of being silently dropped (see below).
- `skipping_a_broken_statement_counts_the_brackets_it_opened` — the cascade the corpus caught: a failure inside a record literal does not make its `}` end the block.
- `publish_sends_one_diagnostic_per_recovered_error` (`src/lsp.rs`) — the LSP consumer, not just `Error::chain()`: three broken statements in one file become three `severity:1` diagnostics in one `publishDiagnostics`.
- `a_broken_file_prints_every_recovered_statement_error` (`src/main.rs`) — the CLI consumer: `main.rs::fail` printed `err.chain()` but nothing asserted it, and `fail` calls `process::exit`, so it cannot be unit-tested in place. Its body is now `fatal_text(errors, file) -> String` (the same joining and per-error `file` placement, `fail` is `eprintln!` + `exit`), and the test drives a real `lithe::compile` of a file with two broken statements through it: two message lines, both naming the file. This is the first consumer-side test of the chain.

**`spec_file` was swallowing the recovered errors** (review finding `find_mjnfhv9f`, high). `parse` assembled its `Error` chain from `parser.errors` plus the terminal error, but `spec_file` built a `Parser` and returned `Ok` while `parser.errors` held errors recovered from a statement inside a spec block — a spec clause reaches `block()` through `if_expr`/`case` → `arm_body`. So `spec for deposit is { ensures if true then { var y : uint := ; } with true else true; }` was **accepted**, with the broken statement dropped, where before recovery it was rejected. That is on the verification path (`lithe specs` / `prove` / `--check-specs`), and it meant the LSP test above would have passed while the spec path still lied. `spec_file` now runs its loop in a closure, pushes the error that ends it, and finishes through `parser.all_errors()` like `parse`, so the same first error is reported (`vault.spec.lithe:2:42: expected an expression, found \`;\``, exit 1) and every subsequent one follows it. The spec-file corpus is small (five `examples/verification/*.spec.lithe`): all still print, `lithe specs` exit 0. The fuzz gate missed this because it ran `abi`/`compile`, which never parse `.spec.lithe` with a broken block; the new `parse.rs` test is the case that gate lacks.

**`skip_stmt` resumed mid-statement and lost its bracket depth** (found by the corpus re-run for the fix above). It scanned forward *from where the statement failed*, so a statement like `emit Foo { indexed amount = 1 };` — which fails at `indexed` with the record's `{` already consumed — left the depth at 0 and stopped at the record's own `}`, one token short of the `;`. The block then saw `}` as its end and the enclosing declaration reported ``expected a declaration, found `}` ``. `examples/reject/event_indexed_emit.lithe` is exactly this shape, and it turned one error into two. `block()` now records the statement's first token and `skip_stmt(start)` rewinds to it before the scan, so the depth counts every bracket the statement opened. The corpus diff against `897f81f` is empty again (38 385 lines) and `event_indexed_emit.lithe` reports its one error. The ceiling of resuming at the statement's *first* token is unchanged: a statement missing its `;` still swallows the next one up to the next `;`.

**What this deliberately does not do.** `skip_stmt` is a bracket-depth scan to the next `;`/`}`, not a "sync on a keyword that can start a statement" heuristic. The grammar has no reserved statement-start keyword (`ident` can begin an assignment, a call, or `delete`), so a keyword scan would resynchronise on identifiers and produce worse cascades than the plain separator scan. The ceiling: a statement missing its `;` swallows the following statement up to the next `;`, so one error becomes one error with a shifted place. A parser that re-parsed with an insertion repair would fix that; nothing in the tree needs it yet.

## S59 5.7 skip_stmt brackets

S30's open medium finding: `skip_stmt` kept **one** counter for `{`, `[` and `(` together, so the kinds were interchangeable and an unclosed paren read as an open brace.

### The bug, traced

Mid-typing state `foo(x;` inside a function body:

1. the `(` sets the (single) depth to 1;
2. the `;` is skipped, because depth ≠ 0;
3. the block's own `}` brings depth back to 0 **and is consumed**;
4. the scan is now past `f`'s closing brace and keeps going. It enters `g`'s params (`(` raises depth, `)` lowers it) and then `g`'s body, whose `{` raises depth again, so none of `g`'s `;` end the statement either. It reaches **`Eof`**. `block()`'s `while self.kind() != Kind::RBrace` therefore never sees an `RBrace`, and `want(Kind::RBrace)` fails at end of file.

The first error is unchanged: the corpus asserts that. But the block ends in the wrong place, so everything after it is wrong — in the shape above the parent reports a spurious ``expected `}`, found end of file`` and loses the second function's real error entirely. That is the same failure class as `event_indexed_emit` (S30's earlier fix), and it defeats the point of 5.7 — the LSP underlines every broken statement, so a cascade is a visibly wrong file.

### The fix

`src/parse.rs::skip_stmt` holds three counters instead of one:

- `}` at `braces == 0` ends the statement where it stands, **unconsumed**, whatever `(`/`[` are still open above it. That is exactly the mid-typing case: the block's `}` belongs to the block, not to the statement's unclosed paren.
- `;` ends the statement only when all three are zero, so a `;` inside `f(a; b)` is still part of the statement.
- `{`/`(`/`[` each increment their own counter; `)`/`]` **saturate** at zero (`saturating_sub`) because a mismatched closer must not underflow a `u32` and turn the statement into a scan to EOF. `}` decrements `braces` and is reached only when `braces > 0`.
- `bump()` is still called at the bottom of every iteration except the exits, so a block always progresses and no loop is possible.

Three counters rather than a stack: the nesting kinds are three and only `braces` gates the exit, so a stack would carry the same information with an allocation and a pop that never affects the decision.

### What it changes in a file that is being typed

```
$ lithe abi bad_paren.lithe          # parent: the block's `}` is eaten, the file runs to EOF
bad_paren.lithe:3:8: expected `)`, found `;`

bad_paren.lithe:11:1: expected `}`, found end of file

$ lithe abi bad_paren.lithe          # this tree: the statement ends at the block's `}` un-consumed
bad_paren.lithe:3:8: expected `)`, found `;`

bad_paren.lithe:8:19: expected an expression, found `;`
```

Line 3 is the first error and it is byte-identical to the parent. The difference is everything after it: the parent consumes the block's `}` as the paren's closer and the scan runs to end of file, so the whole rest of the file is never parsed as declarations and `g`'s real error never appears. With the fix the statement ends at the block's `}` un-consumed, `g` is parsed, and it reports its own error. The `[` case is identical with ``expected `]`, found `;` ``.

The cascade into a following declaration is the same bug when the block's `}` is followed by a `;`:

```
$ lithe abi cascade.lithe             # parent
cascade.lithe:3:8: expected `)`, found `;`

cascade.lithe:4:5: expected a statement, found `external`

cascade.lithe:7:1: expected `}`, found end of file

$ lithe abi cascade.lithe             # this tree
cascade.lithe:3:8: expected `)`, found `;`

cascade.lithe:5:8: expected `)`, found `;`
```

(`cascade.lithe` is `f` with `bar(1;`, then the block's `}` followed by a stray `;`, then `external function g() is { bar(1; }`.) The parent's middle error names `external` as a statement — pure cascade — and its last is the end-of-file artifact. This tree reports each of the two broken functions exactly once.

A `)` or `]` with nothing of its kind open (`bar(];`) and a stray `)` at statement start both parse to an ordinary diagnostic and do not panic — checked by hand against the built binary, which is what the `saturating_sub` is there for.

### Tests added (`src/parse.rs`)

- `an_unclosed_paren_does_not_swallow_the_block` — `bar(1;` then the block's `}`, then a second function with `var y : uint := ;`. Asserts exactly two errors: `(3, "expected `)`, found `;`")` and `(7, "expected an expression, found `;`")`, i.e. the first unchanged, the second reported, and no ``expected a declaration`` in the chain.
- `an_unclosed_bracket_does_not_swallow_the_block` — the same with `a[0;` and ``expected `]`, found `;` ``.

Both fail on the parent. For the paren test the parent's chain is `(3, "expected `)`, found `;`")` plus a spurious `(9, "expected `}`, found end of file")` — line 9 is the empty last line of the 8-line file, since the block's `}` was consumed as the paren's closer and the scan ran to `Eof` — and the second function's real error is missing entirely. `assert_eq!` on the two-element vector is the regression, not a message tweak.

### Proof it changes nothing that was already observable

| gate | result |
|---|---|
| diagnostic corpus: `abi` + `compile` + `specs` + `lint` over every `*.lithe` in `bench/`+`examples/`+`fuzz/`+`std/`, with the exit code, parent `4509901` vs this tree | **41 610 lines, `diff` empty** |
| the same corpus with `errors` (the command that prints the whole chain) | **13 295 lines, `diff` empty** |
| S30's shape, `abi` + `compile --release` over the same files | **38 123 lines, `diff` empty** |
| `make check` (fmt, clippy, `cargo test --locked`, VERIFY, differential 2 000 steps, snapshots, bench gas, playground wasm) | green, exit 0 |
| `cargo test --locked` | 571 + 27 + 1 passed, 2 ignored, 0 failed |
| `cargo test --locked --lib evm::snapshot` | 2 passed — **both bytecode snapshots unchanged** |
| `LITHE_VERIFY=1 cargo test --locked` | 571 passed, 2 ignored, 0 failed |
| `LITHE_FUZZ_STEPS=2000 … evm::differential` | 5 passed |
| LSP diagnostics, `did_change_coalesces_and_erc20_full_diagnostics_are_fast` (`cargo test --locked --bin lithe`, dev test profile, 3 runs each) | **8.14–8.50 ms** this tree vs **8.24–8.38 ms** parent — noise. Unchanged, as it must be: `parse` is 0.14 ms of the frontend (S30) and `skip_stmt` runs only on an already-broken statement, so no valid file reaches it. (S30 quoted 6.9 ms for this test; that was a release build, hence the offset.) |

The corpus diff being empty is the load-bearing result: every file in the repo is either valid or broken in a way that does not reach this shape, so the fix adds errors only where the parent was *wrong* to suppress them. It cannot remove or reorder a first error, because `skip_stmt` runs only after `block()` has already pushed that error.

**Ceiling, unchanged.** A statement missing its `;` still swallows the next statement up to the next `;`, and a `}` inside a `(`-group is now treated as the block's — which is right for the recovery we have (there is no block expression that a bare `}` can close inside parentheses) but would need a real expression end if the language ever grows one. Recorded rather than pre-built.

## S41 6.5 `--timings` and the perf gate

**Plan.** One flag, no new instrumentation: `--timings` sets `LITHE_TIME=1` before any command runs, so it prints the `[time]` line the harness already parses. Then a `perf` CI job that compiles `bench/erc20_full.lithe` seven times in Fast mode at one thread and fails on the best time over 2× the recorded baseline. Bytecode cannot move: the flag only reads the clock on a path the counters already own, and the job changes no source.

### The flag

`main` takes `--timings` out of the arguments, wherever it sits after the command, and sets `LITHE_TIME` before dispatching (`src/main.rs`, `take_timings`). Nothing else changes: `gen::timing()` reads the variable once per process into a `OnceLock`, so a process with `--timings` behaves exactly like `LITHE_TIME=1`. `lithe compile f --fast --timings`:

```text
[time] check=5.85ms backend=35.65ms | emits=1 sum=5.56ms (promote 4.74ms, 58 rounds) | finishes=2 sum=22.02ms (optimize 11.89ms, outline+ 8.91ms) | body 5.42ms
```

`--timings` with no variable prints the same line, and without either there is no line (checked: `grep -c '^\[time\]'` is 1 and 0). `cargo test --bin lithe tests::timings_flag_is_taken_from_anywhere` covers the argument handling, including that the flag is taken from between other arguments and that a command without it is untouched. Documented in `docs/src/pages/tooling/cli.mdx` under **Timings**, and in `lithe`'s usage text.

### The gate

`.github/workflows/ci.yml` gains a `perf` job: `cargo build --release --locked`, then seven timed runs of

```text
LITHE_CACHE_DIR= LITHE_THREADS=1 target/release/lithe compile bench/erc20_full.lithe --fast --timings
```

It fails if the best run exceeds 118 ms, twice the 59 ms recorded for `--fast` on this contract in `## 1.1`. Best-of-7 because a shared runner has noisy neighbours and one slow run says nothing about the compiler; an absolute bar at 2× because the baseline is a wall-clock number of the same shape. The step also fails if the run prints no `[time]` line, so a broken `--timings` cannot make the job pass by measuring nothing.

The script was extracted from the workflow and run here unchanged (load average ~2, 16 cores, release binary):

| run | 1 | 2 | 3 | 4 | 5 | 6 | 7 | best |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| wall ms | 50 | 52 | 53 | 50 | 54 | 53 | 54 | **50** |

50 ms against a 118 ms limit, 42 % of it. A hosted runner's cores are not these cores, so the margin is deliberate: `simplify:` in the workflow names the ceiling (a runner 2.4× slower than this box fails on hardware) and the upgrade path (a self-hosted runner, or a ratio against a reference binary built from the baseline commit in the same job). It is the cheapest form of the check: it reuses the job's one release build.

Lowering `baseline_ms` to 20 and rerunning the same extracted script failed as it should — `::error ... took 52 ms, over 2x the 20 ms baseline`, exit 1 — so the over-limit branch is exercised, not just written. The `perf` job is added to `success`'s `needs`, so a slow run turns the required check red.

### Gates

| gate | result |
|---|---|
| `make check` (fmt, clippy, `cargo test --locked`, `LITHE_VERIFY=1`, differential 2 000 steps, both bytecode snapshots, bench gas, playground wasm) | **green, exit 0** |
| `cargo test --locked --bin lithe` | 28 passed, 0 failed |
| `node docs/check.mjs` against this binary | 296 programs compile as documented |
| the CI step's script, extracted from the workflow and run locally | passes at 50 ms; fails at exit 1 with the `::error` line when the baseline is lowered to 20 ms |
| `actionlint` / `zizmor` on the workflow | **not run here**: actionlint needs Docker, and no Docker daemon is running in this workspace. The YAML parses (`yaml.safe_load`, nine jobs), the script passes `bash -n`, and the job copies the shapes of the existing ones (pinned action hashes, `persist-credentials: false`, `timeout-minutes`) |
| bytecode | unchanged by construction: the change reads no code path that emits, and no source outside `main`'s argument handling (plus docs) differs |

## S50 3.5 closed: met, no new cut

**Obligation.** §5 3.5 asks that per-line `promote`+`optimize` cost from 439 to 1735 ladder lines be ≤ 1.5×. S50 offers two exits: land a cut, or record the step not-taken with the measurement that closes it. There is a third, and it is the one that holds: **the bar was already met by the time this step ran**, by 3.2c and 3.3b(ii), whose numbers were never fed back into the `## 3.5 Ladder after 3.4b` table. That table was taken on a tree the record itself says excluded 3.2b and 3.3b; it says "Re-run this table once 3.2b and 3.3b land", and no step did. Re-running it is the whole of this step.

### Method

`scripts/bench_compile.py --skip-gas --threads 1` over the ladder, cache off (`LITHE_CACHE_DIR` empty), `LITHE_THREADS=1`, 16 cores, one contract per process. Fast is the same script with `--bin` pointed at a wrapper that rewrites `--release` to `--fast`, which is how the original table was taken and keeps the CLI's own default out of the comparison. Five full rounds of the whole ladder per mode; each figure below is the best of the five, and the median is quoted beside the ratio to show the result is not a best-case artifact. Load average 1.4–1.8 at 16 cores, recorded before and after the five rounds.

The direct-command form is the same measurement and is what a reviewer should re-run, from the repo root:

```text
mkdir -p /tmp/ladder && cd /tmp/ladder
for n in 16 64; do python3 /path/to/lithe/scripts/gen_scaling.py $n > n$n.lithe; done
BIN=/path/to/lithe/target/release/lithe
for f in n16 n64; do LITHE_CACHE_DIR= LITHE_TIME=1 LITHE_THREADS=1 "$BIN" compile --fast $f.lithe; done
```

`--fast` and `--release` give the two columns; the `[time]` line's `promote` and `optimize` terms are the numerator. Taking the *minimum* of several runs matters here: one round of this ladder taken at load 13 on the same box and the same binary read the 1735-line rung at 30.3 ms best / 48.1 ms median instead of 15.4 / 15.7, which is enough to invert the conclusion.

### The table

`sum` is `promote`+`optimize`; `µs/line` is `sum` over the line count, min / median of five. `p/emit` is `promote` divided by `emits`.

| N | lines | mode | promote ms | p/emit ms | optimize ms | µs/line min / med | emits/finishes | promote rounds |
|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 16 | 439 | Fast | 0.44 | 0.44 | 5.75 | **14.12 / 15.32** | 1/2 | 4 |
| 32 | 871 | Fast | 0.83 | 0.83 | 7.85 | 9.96 / 10.12 | 1/2 | 4 |
| 64 | 1735 | Fast | 1.72 | 1.72 | 13.79 | **8.95 / 9.03** | 1/2 | 4 |
| 128 | 3463 | Fast | 4.91 | 4.91 | 28.12 | 9.54 / 9.61 | 1/2 | 4 |
| 256 | 6919 | Fast | 14.94 | 7.47 | 64.49 | 11.50 / 11.57 | 2/4 | 5 |
| 16 | 439 | Release | 3.81 | 0.35 | 5.80 | **21.90 / 23.27** | 11/2 | 75 |
| 32 | 871 | Release | 8.27 | 0.75 | 7.92 | 18.61 / 18.79 | 11/2 | 107 |
| 64 | 1735 | Release | 20.37 | 1.85 | 13.85 | **19.74 / 20.18** | 11/2 | 171 |
| 128 | 3463 | Release | 61.23 | 5.57 | 27.89 | 25.88 / 26.09 | 11/2 | 299 |
| 256 | 6919 | Release | 222.64 | 10.12 | 99.13 | 46.53 / 47.14 | 22/5 | 553 |

| 439 → 1735 | min | median | bound |
|---|---:|---:|---:|
| Fast | **0.63×** | 0.59× | 1.50× |
| Release | **0.90×** | 0.87× | 1.50× |

Against the recorded 42.9 µs/line (Fast) and 69.3 µs/line (Release) at 1735 lines, this rung is **4.8× and 3.5× cheaper per line**. The 439-line rung moved much less (19.2 → 14.1 and 34.5 → 21.9, so 1.36× and 1.58×): it pays a fixed per-build cost the bigger file amortises, and 3.2c and 3.3b(ii) barely touch it. The ratio fell because the 439 rung's denominator is small, not because that rung regressed.

**Why the ratio is below 1, and how much of that is fixed cost.** The 439-line rung pays per-build constants the 1735-line file amortises: process start, the `std/evm` load, one `emit` and two `finish`es in Fast. Taking the constant and slope from the first gap alone (439→871) gives **Fast ≈ 3.7 ms fixed + 5.76 µs/line** and **Release ≈ 2.9 ms + 15.2 µs/line**; holding each slope flat to 1735 lines, fixed cost alone predicts a **0.56×** ratio in Fast and **0.77×** in Release. The measured ratios are *higher* in both — 0.63× and 0.90× — and the difference is exactly the slope rising over that span (5.76 → 7.91 µs/line in Fast, 15.2 → 20.9 in Release). So the bar is passed on amortisation, not on linearity: Fast clears it on a fixed constant with room to spare, Release clears it by 0.10× while its own slope is growing.

The per-line *marginal* cost, which is what 3.5's bar stands in for, is therefore not flat in either mode, and keeps rising above the bar's range — Fast **5.76 → 7.91 → 10.14 → 13.43** µs/line and Release **15.2 → 20.9 → 31.8 → 67.3** across the four gaps from 439 to 6919. 3.5's literal 439→1735 window is met, largely on Fast's fixed constant; it is not evidence that the passes are linear, and the rungs above 1735 say so.

### What closed it, and what is left

- **3.2c** (`merge_tails` takes its next-best free pair in the same call) cut `optimize`'s largest term by removing the round a lost pairing used to cost. Ladder 64 Fast `optimize` was 56.2 ms before it and is 13.79 ms here.
- **3.3b(ii)** (batched promotion) cut `promote`'s rounds to 4 at every ladder size and made `promote` per-emit flat: Fast `p/emit` is 0.44 / 0.83 / 1.72 / 4.91 ms at 439 / 871 / 1735 / 3463 lines, so ≈ 1.0 µs per line per emit at each of the first three rungs (0.95–1.00) and 1.42 at 3463. Release `p/emit` climbs faster (0.35 → 1.85 ms, 0.79 → 1.07 µs per line per emit) and its `emits` is 11 rather than 1, so Release pays 11 growing `promote` runs where Fast pays one; that is search cost per candidate, not a superlinear pass, and it is why Release's ratio is 0.90× rather than Fast's 0.63×.
- **Residual, recorded not fixed.** Release is 1.30× per line from 1735 → 3463 and 1.81× from 3463 → 6919, and Fast 1.07× and 1.20×. That is the same `optimize` term 3.2b/3.2c have been chipping at, now pushed above 1735 lines. Nothing in §5 is blocked on it: the 1735-line rung 3.5 names is also §4's "synthetic 1 735-line build ≤ 25 ms", and that target is measured here at **40.0 ms backend / 52.0–53.5 ms wall** (min of 5, Fast) against 43.5 ms backend in `## 3.2c` — flat, still missed, and owned by §4. Closing the residual would need one of 3.2b(ii)'s rejected options (a per-round incremental `flow`, measured at 10–12 % of a loop that is a small part of `outline+`) or a `merge_tails` that merges more per call still. Neither is in scope for a step whose bar is met; they are 6.4 territory.

### Gates

Nothing in this step changes source, so the gates are here to prove the tree the numbers were taken on is the committed tree, not a scratch build.

| gate | result |
|---|---|
| `make check` (fmt, clippy, `cargo test --locked`, `LITHE_VERIFY=1`, differential 2 000 steps, both bytecode snapshots, bench gas, playground wasm) | **green, exit 0** |
| `cargo test --locked` | 571 passed, 2 ignored, 0 failed |
| `cargo test --locked --lib evm::snapshot` | 2 passed — **both bytecode snapshots unchanged** |
| `LITHE_FUZZ_STEPS=2000 … evm::differential` | 5 passed, `fast_matches_release` included |
| `git status` | clean before this edit; the only diff this step adds is `PROGRESS.md` — this record plus the four summary lines it brings into line (the 3.5 task line, the State bullet, the `## S48` obligation list, and a "superseded" note on the old ladder table) |

## Accepted §4 misses

Two of §4's after-Phase-3 headline targets are missed on the finished tree. The human has accepted both as they stand. Neither is re-attempted. The numbers below are the ones already recorded; the linked sections hold the measurements and methods.

| §4 target | baseline | recorded on this tree | target | why accepted |
|---|---|---|---|---|
| LSP diagnostics on a `bench/erc20_full.lithe` edit | ≈ 2 400 ms (§4) | **6.2 ms** (release; `## 5.2a`, after `## 2.6`'s 6.3–6.5 ms) | ≤ 5 ms | The floor is `check` alone at 5.3–5.8 ms (`## 2.6`, `## 5.1c`). The server already skips everything else: the index is lazy, and lint reuses the checked units. |
| Synthetic 1 735-line ladder (N = 64), single build | ≈ 195 ms (§4); 261.6 ms in `baseline.json` | **40.0 ms backend / 52.0–53.5 ms wall** (Fast, min of 5; `## S50 3.5 closed`) | ≤ 25 ms | 3.2c and 3.3b(ii) gave the pass cuts that hold under the gates. The remaining time is `optimize`/`outline+` on code whose bytes are fixed by the snapshot and the 1 % budget. |

Why neither is reachable inside §2's invariants:

- **LSP ≤ 5 ms.** Getting under the bar means making `check` cheaper. §2 forbids touching the checker for speed. The Phase 5 hygiene steps (5.1a–c, 5.2a, 5.4, 5.7) are done and did not move this number past noise.
- **Ladder ≤ 25 ms.** Getting under the bar means another cut to `optimize`, one that either changes the bytes or the gates would not accept. A per-round incremental `flow` measures at 10–12 % of a small loop (`## 3.4b`), and `merge_tails` already takes every free pair it can per call (`## 3.2c`).

Known residual, accepted with the ladder row and owned by no remaining step: per-line cost still grows past 1 735 lines. Release is 1.30× at 3 463 lines and 1.81× at 6 919. Fast is 1.07× and 1.20× (`## S50 3.5 closed`, "Residual, recorded not fixed").

## Handoff

This is the closing note under §3's stop condition. Every §5 box from 0.1 to 6.5 is checked on this branch. Each one either landed or is recorded as not taken with the measurement that closes it.

- **Branch.** `recur/honeyed-trifle`, 110 commits ahead of `origin/main` and 21 behind. It is unpushed by design. `celestiaorg/lithe` does not accept outside PRs, so the deliverable is the reviewed branch plus this file. No PR is opened.
- **Accepted §4 misses.** LSP diagnostics are 6.2 ms against ≤ 5 ms, and the 1 735-line ladder is 40.0 ms backend against ≤ 25 ms. Both are in `## Accepted §4 misses` above.
- **Also missed, not part of that acceptance.** The `erc20_full` Fast compile is 50.4 ms against §4's Phase 3 bar of ≤ 15 ms. The Phase 1 bar (≤ 60 ms) is met. This miss is recorded in `## Comparison with baseline.json` under "Headlines against §4's targets", and it is left for the human to decide.
- **Recorded not taken, with measurements:**
  - **4.1, per-function parallel emit.** Per-body emission is 9.1 % of the Fast backend and 8.2 % of the Release backend, so it caps the speedup at 1.10×. See `## S23 4.1 closed: not taken`.
  - **5.5, index-arena AST.** The change is 1 378 errors in 41 files. Its payoff is 0.08 % of a Release build and 1.2–1.7 % of a Fast build. See `## S32 5.5 closed: not taken`.
  - **3.3, value-numbering stack scheduler.** `promote` is 8.9 % of the Fast backend over `bench/`. 3.3b(ii)'s batched promotion is what landed. See `## S48 3.3 closed: not taken`.
- **Final state.** `make check` passed on this tree for the packaging commit, and both bytecode snapshots are unchanged. The final numbers are in `## Comparison with baseline.json`.
