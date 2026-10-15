"""Compiles example directories through `lithe --standard-json` and prints a SHA-256 of each
output. Every release target must print the same lines."""

import hashlib
import json
import os
import pathlib
import subprocess
import sys

DIRS = ["examples/imports", "examples/stdlib", "examples/uniswap_v2", "examples/verification"]

lithe = sys.argv[1]
env = {**os.environ, "LITHE_CACHE_DIR": ""}
for dir in DIRS:
    sources = {
        path.as_posix(): {"content": path.read_text()}
        for path in sorted(pathlib.Path(dir).glob("*.lithe"))
    }
    request = json.dumps({"language": "Lithe", "sources": sources})
    out = subprocess.run(
        [lithe, "--standard-json"], input=request.encode(), env=env, capture_output=True, check=True
    ).stdout
    errors = [e for e in json.loads(out).get("errors", []) if e["severity"] == "error"]
    if errors:
        sys.exit(f"{dir}: {errors[0]['formattedMessage']}")
    print(f"{hashlib.sha256(out).hexdigest()}  {dir}")
