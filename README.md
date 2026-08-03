# lean-tptp

Total TPTP/TSTP parsing for Lean 4, backed by [Grip](https://github.com/jonaprieto/lean-grip).
It is the small, reusable format layer for tools that need to read ATP problems or results
without depending on an online-prover client.

[![CI](https://github.com/jonaprieto/lean-tptp/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-tptp/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.32.1-blue)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

## Why a separate library?

OATP needs TPTP/TSTP syntax, but ATP clients, proof widgets, corpus tools, and local-prover
adapters can use the same parser without importing networking or prover orchestration. The
implementation lives here once; OATP consumes this package rather than maintaining a fork.

## Quick start

Add the package to `lakefile.lean`:

```lean
require tptp from git
  "https://github.com/jonaprieto/lean-tptp.git"
  @ "main"
```

Parse a complete document or one statement. Both APIs return Grip's positioned errors:

```lean
import TPTP

def source := "include('Axioms/foo.p').\nfof(goal, conjecture, p(a))."

example : Except Grip.ParseError TPTP.Document :=
  TPTP.parseString source

example : Except Grip.ParseError TPTP.Statement :=
  TPTP.parseStatementString "cnf(goal, conjecture, p(a) | ~q(a))."
```

Run the included example locally:

```text
lake exe demo
```

Run the public [`jonaprieto/prop-pack`](https://github.com/jonaprieto/prop-pack) corpus when
it is checked out:

```text
python3 scripts/test-corpus.py ../prop-pack
```

The corpus runner discovers `.p`, `.tptp`, and `.tstp` files and feeds them to the same
total parser used by the library. CI runs the complete `prop-pack` corpus without copying it
into this package.

## What is parsed

The envelope parser is total and accepts the standard statement tags `fof`, `cnf`, `tff`,
`thf`, `tcf`, and `tpi`, preserving unknown tags as `.other`. It also handles:

- `include(...)` directives and optional selections;
- quoted names and nested `()`, `[]`, and `{}` bodies;
- line/block comments and multiline input;
- TSTP annotations, split only at the top-level comma;
- UTF-8 source text through the `String` convenience API.

The formula body is intentionally preserved as source text, so a consumer does not lose
syntax that this library does not interpret. The optional `TPTP.Formula` parser provides a
small first-order AST for atoms, terms, connectives, and quantifiers; it is useful for the
common `fof`/`cnf` fragment and is not a claim to be a complete higher-order TPTP semantics.

```lean
open TPTP

example : Except Grip.ParseError TPTP.Formula.Expr :=
  TPTP.Formula.parseFormulaString "! [X] : (p(X) => q(X))"
```

For terminal presentation, compose the returned `Grip.ParseError` with the ecosystem's
diagnostics frontend. This package stays independent of terminal color, HTTP, and ATP
process management.

## Design guarantees

- Parser recursion uses Grip's fuelled `GParser.fix`; parser definitions are not `partial`.
- Repetition uses Grip's progress-aware graded combinators.
- Parse failures carry byte position, line, column, and expected-token information.
- Raw formula and annotation text is retained for round-tripping and downstream parsers.
- The properties target is audited in CI for unexpected proof axioms.

## Scope

This package parses the source envelope and a deliberately small first-order formula subset.
It does not resolve `include` paths, execute prover output, reconstruct proofs, or validate
the full typed/higher-order TPTP grammar. Those belong in consumers or future typed modules.

## License

Apache 2.0. See [LICENSE](LICENSE).
