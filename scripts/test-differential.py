#!/usr/bin/env python3
"""Check a conservative TPTP fixture subset with E when it is installed."""

import pathlib
import shutil
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: scripts/test-differential.py PATH")

prover = shutil.which("eprover")
if prover is None:
    print("differential syntax check: skipped (eprover is not installed)")
    raise SystemExit(0)

root = pathlib.Path(sys.argv[1])
files = sorted(path for path in root.rglob("*") if path.is_file())
if not files:
    raise SystemExit(f"no differential fixtures under: {root}")

for path in files:
    result = subprocess.run(
        [prover, "--syntax-only", str(path)],
        text=True,
        capture_output=True,
    )
    if result.returncode:
        sys.stderr.write(result.stderr)
        raise SystemExit(f"eprover rejected {path}")

print(f"differential syntax check: {len(files)} files accepted by eprover")
