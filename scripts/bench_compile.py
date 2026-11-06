#!/usr/bin/env python3
# simplify: release only until `lithe compile --fast` (task 1.1). The N-thread sample is
# compile only (`lithe abi` ignores LITHE_THREADS). wall_s is perf_counter because
# /usr/bin/time %e is centiseconds here; that figure is still stored as time_wall_s.
"""Time `lithe abi` and `lithe compile`. See scripts/README.md."""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LADDER = (16, 32, 64, 128, 256)
DUR = re.compile(r"([0-9]+(?:\.[0-9]+)?)(ns|µs|μs|us|ms|s)\Z")
TIME_LINE = re.compile(
    r"\[time\] check=(\S+) backend=(\S+) \| "
    r"emits=(\d+) sum=(\S+) \(promote (\S+)\) \| "
    r"finishes=(\d+) sum=(\S+) \(optimize (\S+), outline\+ (\S+)\)"
)
SCALE = {"ns": 1e-9, "us": 1e-6, "µs": 1e-6, "μs": 1e-6, "ms": 1e-3, "s": 1.0}


def dur_s(text):
    match = DUR.match(text)
    if not match:
        raise SystemExit(f"bad duration {text!r}")
    return float(match.group(1)) * SCALE[match.group(2)]


def phases(stderr):
    rows = []
    for line in stderr.splitlines():
        match = TIME_LINE.search(line.strip())
        if match:
            rows.append(match.groups())
    if not rows:
        return None
    last = rows[-1]
    return {
        "check_s": round(sum(dur_s(row[0]) for row in rows), 6),
        "backend_s": round(sum(dur_s(row[1]) for row in rows), 6),
        "emits": int(last[2]),
        "emit_s": round(dur_s(last[3]), 6),
        "promote_s": round(dur_s(last[4]), 6),
        "finishes": int(last[5]),
        "finish_s": round(dur_s(last[6]), 6),
        "optimize_s": round(dur_s(last[7]), 6),
        "outline_s": round(dur_s(last[8]), 6),
    }


def is_program(src):
    for line in src.splitlines():
        if (
            line.startswith("external ")
            or line.startswith("upgradeable")
            or line.startswith("contract ")
            or line.startswith("migrate ")
        ):
            return True
        stripped = line.lstrip()
        if stripped.startswith("use ") and " exposing" in line:
            return True
    return False


def contract_count(src):
    return sum(line.startswith("contract ") for line in src.splitlines())


def needs_deploy_args(src):
    lines = src.splitlines()
    if any(line.strip() == "upgradeable" for line in lines):
        return False
    for line in lines:
        body = line.lstrip()
        while body.startswith("payable "):
            body = body[len("payable ") :]
        if body.startswith("deploy(") and not body.startswith("deploy()"):
            return True
    return False


def keep_example(rel, src):
    """Same gate as `differential_targets` for files under examples/."""
    if rel.startswith("examples/reject/") or rel.endswith(".spec.lithe"):
        return False
    return is_program(src) and contract_count(src) <= 1 and not needs_deploy_args(src)


def walk_lithe(directory):
    found = []
    for dirpath, dirnames, filenames in os.walk(directory):
        dirnames.sort()
        for name in sorted(filenames):
            if name.endswith(".lithe") and not name.endswith(".spec.lithe"):
                found.append(Path(dirpath) / name)
    return found


def repo_targets():
    """(relpath, absolute path) for bench/*.lithe and filtered examples."""
    targets = []
    bench = ROOT / "bench"
    for path in sorted(bench.glob("*.lithe")):
        targets.append((f"bench/{path.name}", path))
    for path in walk_lithe(ROOT / "examples"):
        rel = path.relative_to(ROOT).as_posix()
        src = path.read_text()
        if keep_example(rel, src):
            targets.append((rel, path))
    return targets


def run_env(threads):
    env = os.environ.copy()
    env["LITHE_CACHE_DIR"] = ""
    env["LITHE_TIME"] = "1"
    env["LITHE_THREADS"] = str(threads)
    env.pop("LITHE_BENCH_OUT", None)
    env.pop("LITHE_BENCH_GAS", None)
    return env


def measure(cmd, cwd, threads):
    with tempfile.NamedTemporaryFile(prefix="lithe-time-") as stamp:
        started = time.perf_counter()
        proc = subprocess.run(
            ["/usr/bin/time", "-f", "%e %U %S %M", "-o", stamp.name, "--", *cmd],
            cwd=cwd,
            env=run_env(threads),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        wall = time.perf_counter() - started
        text = Path(stamp.name).read_text().split()
    if len(text) != 4:
        raise SystemExit(f"time failed for {cmd}: {text!r}")
    user, sys_ = float(text[1]), float(text[2])
    return {
        "wall_s": round(wall, 6),
        "time_wall_s": float(text[0]),
        "cpu_s": round(user + sys_, 4),
        "rss_kb": int(text[3]),
        "code": proc.returncode,
        "stderr": proc.stderr.decode(errors="replace"),
    }


def object_len(node):
    hex_text = node["object"]
    if not hex_text.startswith("0x") or len(hex_text) % 2:
        raise SystemExit(f"bad bytecode object {hex_text[:16]!r}")
    return (len(hex_text) - 2) // 2


def artifact_bytes(out_dir):
    creation = runtime = 0
    if not out_dir.is_dir():
        return creation, runtime
    for path in out_dir.rglob("*.json"):
        data = json.loads(path.read_text())
        if isinstance(data.get("bytecode"), dict):
            creation += object_len(data["bytecode"])
        if isinstance(data.get("deployedBytecode"), dict):
            runtime += object_len(data["deployedBytecode"])
    return creation, runtime


def lines_per_s(lines, wall_s):
    if wall_s <= 0:
        return None
    return round(lines / wall_s, 1)


def timed(cmd, cwd, threads, lines, compile_out=None):
    row = measure(cmd, cwd, threads)
    if row["code"] != 0:
        raise SystemExit(f"{' '.join(cmd)} failed ({row['code']}):\n{row['stderr']}")
    out = {
        "wall_s": row["wall_s"],
        "time_wall_s": row["time_wall_s"],
        "cpu_s": row["cpu_s"],
        "rss_kb": row["rss_kb"],
        "lines_per_s": lines_per_s(lines, row["wall_s"]),
    }
    if compile_out is None:
        return out
    creation, runtime = artifact_bytes(compile_out)
    if runtime <= 0:
        raise SystemExit(f"{' '.join(cmd)} wrote no runtime code:\n{row['stderr']}")
    got = phases(row["stderr"])
    if got is None:
        raise SystemExit(f"{' '.join(cmd)} printed no [time] line:\n{row['stderr']}")
    out["creation_bytes"] = creation
    out["runtime_bytes"] = runtime
    out["phases"] = got
    return out


def compile_one(lithe, src, threads, lines):
    """One file in its own directory, so `out/` is that contract's bytecode."""
    with tempfile.TemporaryDirectory(prefix="lithe-bench-") as work:
        work = Path(work)
        stage = work / "in"
        stage.mkdir()
        (stage / src.name).symlink_to(src.resolve())
        return timed(
            [lithe, "compile", "in"],
            work,
            threads,
            lines,
            compile_out=work / "out",
        )


def abi_one(lithe, src, lines):
    with tempfile.TemporaryDirectory(prefix="lithe-bench-") as work:
        return timed([lithe, "abi", str(src.resolve())], work, 1, lines)


def one_target(lithe, rel, src, threads_n):
    text = src.read_text()
    lines = len(text.splitlines())
    print(f"bench {rel} ({lines} lines)", file=sys.stderr)
    return {
        "lines": lines,
        "release": {
            "1": {
                "abi": abi_one(lithe, src, lines),
                "compile": compile_one(lithe, src, 1, lines),
            },
            str(threads_n): {"compile": compile_one(lithe, src, threads_n, lines)},
        },
    }


def ladder_files(dest):
    script = ROOT / "scripts" / "gen_scaling.py"
    made = []
    for n in LADDER:
        src = subprocess.check_output([sys.executable, str(script), str(n)], text=True)
        path = dest / f"n{n}.lithe"
        path.write_text(src)
        made.append((f"scaling/n{n}.lithe", path))
    return made


def gas_report():
    with tempfile.TemporaryDirectory(prefix="lithe-gas-") as work:
        dest = Path(work) / "gas.json"
        env = os.environ.copy()
        env["LITHE_BENCH_OUT"] = str(dest)
        env["LITHE_CACHE_DIR"] = ""
        print("bench gas", file=sys.stderr)
        proc = subprocess.run(
            [
                "cargo",
                "test",
                "--release",
                "--offline",
                "--lib",
                "evm::bench_gas::bench_gas",
                "--",
                "--exact",
            ],
            cwd=ROOT,
            env=env,
        )
        if proc.returncode != 0 or not dest.is_file():
            raise SystemExit("bench gas failed")
        return json.loads(dest.read_text())


def collect(lithe, threads_n, only, skip_gas):
    lithe = str(Path(lithe).resolve())
    targets = {}
    chosen = repo_targets()
    with tempfile.TemporaryDirectory(prefix="lithe-ladder-") as ladder:
        chosen.extend(ladder_files(Path(ladder)))
        if only:
            chosen = [item for item in chosen if item[0] in only]
            if len(chosen) != len(only):
                missing = sorted(set(only) - {rel for rel, _ in chosen})
                raise SystemExit(f"unknown target {missing}")
        # The ladder directory is removed when this block ends.
        for rel, path in chosen:
            targets[rel] = one_target(lithe, rel, path, threads_n)
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    report = {
        "commit": commit,
        "profile": "release",
        "opt": "release",
        "threads_n": threads_n,
        "targets": targets,
    }
    if not skip_gas:
        report["gas"] = gas_report()
    return report


def self_check():
    sample = (
        "[time] check=11.2ms backend=2.37s | emits=99 sum=2.1s (promote 1.8s) | "
        "finishes=91 sum=500ms (optimize 400.5ms, outline+ 100µs)"
    )
    got = phases(sample)
    assert got["check_s"] == round(0.0112, 6)
    assert got["backend_s"] == 2.37
    assert got["emits"] == 99 and got["finishes"] == 91
    assert got["outline_s"] == round(100e-6, 6)
    two = phases(sample + "\n" + sample)
    assert two["check_s"] == round(0.0224, 6) and two["emits"] == 99
    rels = {rel for rel, _ in repo_targets()}
    assert "bench/erc20_full.lithe" in rels
    assert "bench/counter.lithe" in rels
    assert "examples/counter.lithe" in rels
    assert "examples/factory.lithe" not in rels
    assert "examples/deploy.lithe" not in rels
    assert not any(rel.startswith("examples/reject/") for rel in rels)
    assert not any(rel.endswith(".spec.lithe") for rel in rels)
    assert abs(dur_s("3ns") - 3e-9) < 1e-18
    print(f"self-check ok ({len(rels)} repo targets)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-o", "--out", type=Path, help="write the JSON report here")
    parser.add_argument("--bin", type=Path, help="lithe binary (default target/release/lithe)")
    parser.add_argument("--threads", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--only", action="append", default=[], help="relpath to measure")
    parser.add_argument("--skip-gas", action="store_true")
    parser.add_argument("--self-check", action="store_true")
    args = parser.parse_args()
    if args.self_check:
        self_check()
        return
    lithe = args.bin or (ROOT / "target" / "release" / "lithe")
    if not lithe.is_file():
        raise SystemExit(f"no compiler at {lithe}; cargo build --release")
    if args.threads < 1:
        raise SystemExit("--threads needs a positive count")
    report = collect(lithe, args.threads, set(args.only), args.skip_gas)
    text = json.dumps(report, indent=2) + "\n"
    if args.out:
        args.out.write_text(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
