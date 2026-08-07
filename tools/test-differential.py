#!/usr/bin/env python3
"""Compare the Lean parser with E on a conservative common subset."""

import pathlib
import re
import shutil
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: tools/test-differential.py PATH")

root = pathlib.Path(sys.argv[1])
files = sorted(path for path in root.rglob("*") if path.is_file())
if not files:
    raise SystemExit(f"no differential fixtures under: {root}")

typed = subprocess.run(
    ["lake", "exe", "corpus", "--", "--typed", *(str(path) for path in files)],
    check=False,
    text=True,
    capture_output=True,
)
sys.stdout.write(typed.stdout)
if typed.returncode:
    sys.stderr.write(typed.stderr)
    raise SystemExit("Lean rejected a differential fixture")
counts = re.search(r"TPTP typed corpus: \d+ files, (\d+) FOF, (\d+) CNF, (\d+) TFF", typed.stdout)
if counts is None or sum(int(counts.group(index)) for index in (1, 2, 3)) == 0:
    raise SystemExit("differential fixtures contain no typed FOF/CNF/TFF statements")

prover = shutil.which("eprover")
if prover is None:
    print("differential syntax check: Lean accepted; E comparison skipped")
    raise SystemExit(0)

version = subprocess.run([prover, "--version"], check=True, text=True, capture_output=True)
version_line = version.stdout.splitlines()[0] if version.stdout else "unknown version"

for path in files:
    result = subprocess.run(
        [prover, "--syntax-only", str(path)],
        text=True,
        capture_output=True,
    )
    if result.returncode:
        sys.stderr.write(result.stderr)
        raise SystemExit(f"eprover rejected {path}")

print(f"differential syntax check: {len(files)} files accepted by Lean and {version_line}")
