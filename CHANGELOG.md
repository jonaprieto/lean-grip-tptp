# Changelog

## 0.5.4 — 2026-08-13

- Totalize the straightforward pure renderers and validators.

## 0.5.3 — 2026-08-12

- Adopt Lean v4.33.0 and precommit-lean v0.1.6.

## 0.5.2 — 2026-08-12

- Adopt the shared `precommit-lean` hooks and refresh them to the pinned release.
- Rewrite the README concisely, correct the repository links, and drop the version number
  from it; the lakefile is the only place a pin belongs.

## 0.5.0

- Complete the TFF1 correctness pass for polymorphic type substitution, alpha-renaming,
  explicit instantiation, type-constructor arity, and scoped validation.
- Add executable property coverage for type-expression operations and regression checks for
  parser, renderer, and validator behavior.
- Bump the package and toolchain metadata to Lean 4.32.2.

## 0.4.0

- Add TF1 rank-1 polymorphic types, fixed-arity constructors, explicit instantiation,
  capture-avoiding substitution, and alpha-renaming.

## 0.3.0

- Add total TF0/TFF syntax for typed formulas, declarations, product signatures, and equality.
- Add TF0 validation for declaration order, default typing, variable scope, arity, and arithmetic.
- Add TFF rendering, conformance cases, official tutorial fixture, corpus counts, and E checks.
- Extend the demo and BNF/conformance documentation to cover the TFF boundary.

## 0.2.1

- Pin the untyped FOF/CNF target to TPTP BNF v9.3.0.1 with a checked-in reference note.
- Add a production conformance matrix with malformed-input cases and semantic validation
  for standard defined symbols.
- Make CI run the matrix, typed corpus validation, and a mandatory Lean/E differential check.
- Accept underscore-bearing defined and system names and formula-role subroles.

## 0.2.0

- Add shared first-order terms and atoms.
- Add total FOF and CNF formula parsers with kind-aware statement helpers.
- Add canonical FOF/CNF rendering and FOF binding validation.
- Add official PUZ001+1 and SYN000-1 fixtures, typed corpus counts, and optional E syntax
  differential checks.
- Keep the raw TPTP/TSTP envelope API lossless for unsupported dialects and annotations.
