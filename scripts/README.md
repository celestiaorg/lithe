# scripts

`gen_scaling.py N` prints a synthetic contract of N independent entrypoints (a loop, a map write, and an event each).

`bench_compile.py` times the release compiler and writes JSON:

- targets: `bench/*.lithe`, `examples/` with the same filter as `differential_targets` (no `examples/reject/`, one contract, no constructor arguments), and the ladder at N = 16, 32, 64, 128, 256
- each target: `lithe abi` and `lithe compile --release` at `LITHE_THREADS=1`, then `lithe compile --release` at `LITHE_THREADS` = the machine's CPU count. `--release` is required: the CLI defaults to fast
- `LITHE_CACHE_DIR` is set empty and `LITHE_TIME=1` is set, so the run is a real compile and stderr carries the `[time]` breakdown
- wall time is `time.perf_counter` around the process (`wall_s`); `/usr/bin/time -f '%e %U %S %M'` supplies centisecond `time_wall_s`, CPU seconds, and peak RSS in KiB
- compile is a directory holding only that file, so `out/` has creation and runtime bytecode (runtime bytes sum every contract and facet artifact)
- `lines_per_s` is the file's line count divided by `wall_s`
- `gas` is the `evm::bench_gas::bench_gas` report (`runtime_bytes`, `deploy_gas`, `gas`, `outcomes`), keyed by `bench/run.py` suite name

```
cargo build --release
python3 scripts/bench_compile.py -o baseline.json
python3 scripts/bench_compile.py --self-check
```

Only release is measured. Fast rows are task 1.2.
