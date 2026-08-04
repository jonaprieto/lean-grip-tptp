# FOF/CNF and TF0/TF1 TFF conformance

This release targets the untyped FOF/CNF productions and the TF0/TF1 TFF profiles in
TPTP syntax BNF **v9.3.0.1**.
The versioned reference note is recorded in [`notes/TPTP-Syntax-BNF.md`](notes/TPTP-Syntax-BNF.md).
The official BNF remains authoritative; this file records our evidence and boundary.

## What is covered

| Area | Evidence |
| --- | --- |
| FOF terms and atoms | `test/Conformance.lean`, typed fixture corpus |
| Equality and inequality | positive and negative matrix cases |
| Defined and system symbols | lexical cases plus `FOF.validate` checks |
| Numeric and quoted terms | integer, rational, real, exponent, quote, back-quote, distinct-object cases |
| FOF quantifiers | universal, existential, multiple variables, scope tests |
| FOF connectives | all six non-associative and both associative connectives |
| CNF literals and clauses | positive, negative, parenthesized, equality, nested clause cases |
| TFF formulas and TF0/TF1 declarations | `test/Conformance.lean`, typed fixtures |
| TFF types and signatures | built-in/user types, product domains, type constructors, predicates, functions |
| TFF1 polymorphism | `!>` signatures, explicit type arguments, substitution, alpha-renaming |
| TFF semantic validation | declaration order, default typing, scope, kind/arity, equality, arithmetic |
| Comments and whitespace | line/block comment and token-boundary cases |
| Malformed input | close negative cases for every major production family |
| Canonical output | parse/render/parse tests in `test/Tests.lean` |
| Corpus regression | pinned TPTP fixtures and the `prop-pack` envelope corpus |
| Independent parser | conservative E syntax differential fixture |

The checked-in official problem fixtures are intentionally small and stable. Their source
headers identify the TPTP release from which they were copied; the current BNF revision is
recorded separately above.

| Fixture | SHA-256 |
| --- | --- |
| `test/fixtures/fof/PUZ001+1.p` | `8cd5b3708b1e915fa3ee426ae6520c53c24b9ed7b675ea2f71c8b99ceae10b7e` |
| `test/fixtures/cnf/SYN000-1.p` | `35ee8d0957eb69b5edc101f112d0d37d5276428cd863e5d4d86db5c9b29ed03a` |
| `test/fixtures/tff/PUZ031_1.p` | `cb15ce71a5679960d397c11861ca1cd9f6e7ee73b78b49d8b0edf7319b348588` |
| `test/fixtures/tff/PUZ139_1.p` | `89112288b4425efe87aebe38ff4425a0cc9461c75fca9cfad0cbccb8fc803b9d` |

Run the local gate with:

```text
lake build TPTP TPTP.Properties demo tests conformance corpus
lake exe tests
lake exe conformance
python3 scripts/test-corpus.py --typed test/fixtures
python3 scripts/test-differential.py test/fixtures/differential
```

The E check is deliberately optional locally because E is not a library dependency. CI
installs E and records its reported version; the typed matrix and corpus checks remain
mandatory everywhere. E 3.2.5 does not parse TF1 `!>` signatures, so the differential
fixture intentionally covers only the shared FOF/CNF/TF0 subset; TF1 conformance uses
the official examples and the typed validator.

## Syntax versus validation

The parser returns the typed syntax tree. `TPTP.FOF.validate` and `TPTP.CNF.validate` then
check properties that are not encoded by the grammar alone:

- every variable occurrence is bound;
- binders are non-empty and contain no duplicate names;
- standard `$`-defined predicates and terms are recognized;
- defined propositions have no arguments;
- defined predicates have their standard built-in arity;
- CNF literals use the same defined/system symbol rules;
- `$$` system symbols remain extensible.

TFF declaration consistency and cross-statement arity environments are checked by
TPTP.TFF.validateDocument, while validateFormula remains useful for one formula with
an explicit starting signature. TF1 declarations bind type variables with `!>`; formula
binders use `![A:$tType]`, and each use of a polymorphic symbol supplies those type
arguments before its term arguments.

## Explicit boundary

The typed FOF parser excludes FOFX sequents because the official BNF labels them “not yet
in use”. This release implements TF0/TF1 TFF, not TXF boolean terms, tuples, conditionals,
lets, or subtype syntax. THF, TCF, TPI, non-classical forms,
structured TSTP annotations, include resolution, and proof reconstruction remain
raw-envelope features or future modules.

The envelope parser is intentionally more tolerant: it preserves unknown statement kinds,
roles, annotations, and formula text. Tolerant envelope acceptance must not be counted as
typed FOF/CNF conformance.

## Release rule

A typed-language change is conformant only when it updates the production matrix, adds
positive and negative regression cases, preserves the pinned corpus, validates declaration
order and types where applicable, and passes the independent differential check when the
fixture is in the common supported subset. Any differential disagreement is reported with
the file and oracle version and must be classified before release.
