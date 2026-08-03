# Changelog

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
