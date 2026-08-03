#!/usr/bin/env python3
"""Run the Lean parser over a local TPTP/TSTP corpus."""

import pathlib
import subprocess
import sys

typed = len(sys.argv) > 1 and sys.argv[1] == "--typed"
paths = sys.argv[2:] if typed else sys.argv[1:]
if len(paths) != 1:
    raise SystemExit("usage: scripts/test-corpus.py [--typed] PATH")

root = pathlib.Path(paths[0])
if not root.is_dir():
    raise SystemExit(f"not a directory: {root}")

files = sorted(
    path
    for path in root.rglob("*")
    if path.is_file() and path.suffix.lower() in {".p", ".tptp", ".tstp"}
)
if not files:
    raise SystemExit(f"no TPTP files under: {root}")

arguments = ["lake", "exe", "corpus", "--"]
if typed:
    arguments.append("--typed")
subprocess.run([*arguments, *(str(path) for path in files)], check=True)
