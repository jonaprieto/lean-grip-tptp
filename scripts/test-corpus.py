#!/usr/bin/env python3
"""Run the Lean parser over a local TPTP/TSTP corpus."""

import pathlib
import subprocess
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: scripts/test-corpus.py PATH")

root = pathlib.Path(sys.argv[1])
if not root.is_dir():
    raise SystemExit(f"not a directory: {root}")

files = sorted(
    path
    for path in root.rglob("*")
    if path.is_file() and path.suffix.lower() in {".p", ".tptp", ".tstp"}
)
if not files:
    raise SystemExit(f"no TPTP files under: {root}")

subprocess.run(["lake", "exe", "corpus", "--", *(str(path) for path in files)], check=True)
