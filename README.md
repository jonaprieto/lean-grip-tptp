# tptp

[![CI](https://github.com/jonaprieto/lean-tptp/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-tptp/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean%204-library-5f5f5f)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Total TPTP/TSTP parsing for Lean 4, backed by [`grip`](https://github.com/jonaprieto/lean-grip).

## Install

```lean
require tptp from git
  "https://github.com/jonaprieto/lean-tptp.git" @ "v0.5.1"
```

## Quick start

```lean
import TPTP

def source := "fof(goal, conjecture, p(a))."
example : Except Grip.ParseError TPTP.Document := TPTP.parseString source
example : Except Grip.ParseError TPTP.Statement :=
  TPTP.parseStatementString "cnf(goal, conjecture, p(a) | ~q(a))."
```

The envelope parser handles `fof`, `cnf`, `tff`, `thf`, `tcf`, `tpi`, includes, comments,
annotations, and nested bodies. Typed modules provide FOF, CNF, and TF0/TF1 TFF terms, formulas,
declarations, and validation. Raw formula text remains available for consumers that need syntax
outside the typed modules.

## Verification

```sh
lake build TPTP TPTP.Properties demo tests
lake exe conformance
python3 tools/test-corpus.py --typed test/fixtures
```

The checked-in fixtures and BNF matrix define the conformance gate. Terminal presentation and ATP
process management belong to consuming packages.

## Related projects

[`oatp`](https://github.com/jonaprieto/oatp) uses TPTP for local and online prover orchestration.

## License

Apache-2.0.
