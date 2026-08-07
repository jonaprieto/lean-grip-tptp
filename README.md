# lean-tptp

Total TPTP/TSTP parsing for Lean 4, backed by [Grip](https://github.com/jonaprieto/lean-grip).
It is the small, reusable format layer for tools that need to read ATP problems or results
without depending on an online-prover client.

[![CI](https://github.com/jonaprieto/lean-tptp/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-tptp/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.32.2-blue)](lean-toolchain)
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
  @ "v0.5.0"
```

Parse a complete document or one statement. The envelope API returns Grip's positioned
errors, while typed formula parsers additionally check the statement kind:

```lean
import TPTP

def source := "include('Axioms/foo.p').\nfof(goal, conjecture, p(a))."

example : Except Grip.ParseError TPTP.Document :=
  TPTP.parseString source

example : Except Grip.ParseError TPTP.Statement :=
  TPTP.parseStatementString "cnf(goal, conjecture, p(a) | ~q(a))."

example : Except TPTP.FormulaError TPTP.FOF.Formula :=
  match TPTP.parseStatementString "fof(goal, conjecture, ! [X] : p(X))." with
  | .ok statement => TPTP.FOF.parseStatementFormula statement
  | .error error => .error (.syntax error)
```

Run the included example locally:

```text
lake exe demo
```

Run the public [`jonaprieto/prop-pack`](https://github.com/jonaprieto/prop-pack) envelope
corpus when it is checked out:

```text
python3 tools/test-corpus.py ../prop-pack
```

The typed fixture corpus exercises the FOF/CNF ASTs and validators, plus TF0/TF1 TFF:

```text
python3 tools/test-corpus.py --typed test/fixtures
```

The FOF/CNF conformance matrix is checked against the versioned BNF reference:

```text
lake exe conformance
```

See [`CONFORMANCE.md`](CONFORMANCE.md) and the [BNF note](notes/TPTP-Syntax-BNF.md) for
the production coverage, negative cases, corpus boundary, and release gate.

The optional differential check uses E's independent TPTP parser for a conservative common
subset when `eprover` is installed:

```text
python3 tools/test-differential.py test/fixtures/differential
```

The corpus runner discovers `.p`, `.tptp`, and `.tstp` files. CI runs the complete
`prop-pack` envelope corpus and the checked-in typed fixtures.

## What is parsed

The envelope parser is total and accepts the standard statement tags `fof`, `cnf`, `tff`,
`thf`, `tcf`, and `tpi`, preserving unknown tags as `.other`. It also handles:

- `include(...)` directives and optional selections;
- quoted names and nested `()`, `[]`, and `{}` bodies;
- line/block comments and multiline input;
- TSTP annotations, split only at the top-level comma;
- UTF-8 source text through the `String` convenience API.

The formula body is intentionally preserved as source text, so a consumer does not lose
syntax that this library does not interpret. The typed modules provide shared first-order
terms/atoms plus FOF formulas, CNF clauses, and TF0/TF1 TFF formulas:

```lean
import TPTP

example : Except Grip.ParseError TPTP.FOF.Formula :=
  TPTP.FOF.parseFormulaString "! [X] : (p(X) => q(X))"

example : Except Grip.ParseError TPTP.CNF.Clause :=
  TPTP.CNF.parseFormulaString "p(a) | ~(q(a))"

example : Except Grip.ParseError TPTP.TFF.Declaration :=
  TPTP.TFF.parseTypeDeclarationString "owns: (human * cat) > $o"

example : Except Grip.ParseError TPTP.TFF.Formula :=
  TPTP.TFF.parseFormulaString "![H:human] : owns(john, H)"

example : Except Grip.ParseError TPTP.TFF.Declaration :=
  TPTP.TFF.parseTypeDeclarationString
    "lookup: !>[A:$tType, B:$tType] : ((map(A, B) * A) > B)"
```

`TPTP.FOF.validate` checks variable scope, empty binders, duplicate binders, and defined
symbol usage. `TPTP.CNF.validate` checks the same shared symbol rules; CNF variables are
implicitly universally quantified. `TPTP.TFF.validateDocument` checks TF0/TF1 declarations,
typed variables, type constructors, explicit polymorphic arguments, default typing, arity,
equality, and arithmetic overloads in source order. A singleton `$false` body is represented
as the empty clause.

TFF statements use the role-aware body parser: declarations in `type` statements become
`TPTP.TFF.Body.declaration`, while all other `tff` statements become
`TPTP.TFF.Body.formula`. Parse a document first, map its TFF statements through
`TPTP.TFF.parseStatementBody`, then pass the resulting bodies to
`TPTP.TFF.validateDocument`.

```lean
open TPTP

example : Except Grip.ParseError TPTP.Formula.Expr :=
  TPTP.Formula.parseFormulaString "! [X] : (p(X) => q(X))"
```

For terminal presentation, compose the returned `Grip.ParseError` with the ecosystem's
diagnostics frontend. This package stays independent of terminal color, HTTP, and ATP
process management.

## Design guarantees

- Parser recursion uses Grip's fuelled `GParser.fix`; typed parser definitions are not
  `partial`.
- Repetition uses Grip's progress-aware graded combinators.
- Parse failures carry byte position, line, column, and expected-token information.
- Raw formula and annotation text is retained for round-tripping and downstream parsers.
- FOF and TFF rendering fully parenthesize binary formulas; typed render/parse round trips
  are tested on checked-in examples.
- TF1 type substitution and alpha-renaming are pure operations covered by executable tests.
- The properties target is audited in CI for unexpected proof axioms.

## Scope

The typed FOF/CNF implementation targets the untyped productions in the official TPTP BNF
revision v9.3.0.1. The TFF implementation targets TF0 and TF1: atomic built-in/user types,
product-style first-order signatures, fixed-arity type constructors, rank-1 polymorphic
signatures, explicit type arguments, typed/default-typed variables, equality, defined
arithmetic, and declaration-order checking. Its production matrix and pinned fixtures are
documented in `CONFORMANCE.md` and the BNF note. TXF boolean terms, tuples, conditionals,
lets, subtypes, THF, non-classical variants, structured TSTP annotations, and include
resolution remain raw-envelope or future modules.

## License

Apache 2.0. See [LICENSE](LICENSE).
