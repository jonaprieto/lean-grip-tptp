# lean-grip-tptp

[![CI](https://github.com/jonaprieto/lean-grip-tptp/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-grip-tptp/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/jonaprieto/lean-grip-tptp?display_name=tag&sort=semver)](https://github.com/jonaprieto/lean-grip-tptp/releases)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.33.1-6f42c1)](lean-toolchain)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-4c8bf5)](https://jonaprieto.github.io/lean-grip-tptp/)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

Total TPTP/TSTP parsing for Lean 4, backed by [`grip`](https://github.com/jonaprieto/lean-grip).

## Development

This project is maintained by its author with AI-assisted development tools.
Changes are reviewed, tested, and remain the maintainer's responsibility.

## Install

```lean
require tptp from git
  "https://github.com/jonaprieto/lean-grip-tptp.git" @ "v0.5.3"
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
