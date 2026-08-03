# TPTP grammar roadmap

The `v0.1.x` parser is a stable, lossless envelope layer. It recognizes statement
boundaries and preserves formula text even when the formula language is not yet modeled.
The grammar work below is deliberately incremental: each stage must be useful, testable,
and releasable before the next language family is added.

## References

- [TPTP Language](https://tptp.org/UserDocs/TPTPLanguage/TPTPLanguage.shtml): language
  hierarchy, types, arithmetic, higher-order features, and non-classical forms.
- [TPTP BNF](https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html): authoritative syntax
  productions and precedence.
- [TPTP ANTLR grammar](https://tptp.org/UserDocs/TPTPLanguage/TPTP.g4): an independent
  executable grammar useful for differential checks.
- [Problem format guide](https://tptp.org/UserDocs/QuickGuide/Problems.html) and
  [derivation format guide](https://tptp.org/UserDocs/QuickGuide/Derivations.html):
  annotated formula and TSTP expectations.
- [prop-pack](https://github.com/jonaprieto/prop-pack): pinned local regression corpus.
- [Grip](https://github.com/jonaprieto/lean-grip): parser combinators and positioned errors.
- OATP: first integration consumer and source of recorded prover-output fixtures.

The implementation must not silently treat one parser as a complete implementation of every
TPTP dialect.

## Rules for every stage

- Keep the raw envelope API source-compatible and lossless.
- Put each dialect in its own module; share tokens, names, positions, and delimiters.
- Separate parsing from semantic validation and type checking. A syntactically valid
  expression may still have an invalid type or undeclared symbol.
- Keep parser recursion total and retain Grip's positioned errors.
- Add positive fixtures, malformed-input fixtures, and round-trip tests before expanding
  the grammar.
- Test both the official examples and a pinned corpus snapshot. Record accepted/rejected
  counts so corpus drift is visible.
- Add a renderer only when its invariants are defined; otherwise retain the original text.
- Audit proof axioms, style, `git diff --check`, and the complete test suite in CI.

## Deliverables for each stage

- A documented AST and public module boundary for the dialect.
- Total Grip-backed parser entry points with positioned errors.
- A lossless source representation or a proven canonical renderer.
- Separate validation/type-checking functions where syntax alone is insufficient.
- Positive official fixtures and negative fixtures for every new production family.
- Corpus results recorded by dialect, including accepted, rejected, and intentionally raw
  statements.
- Examples showing the public API and an OATP integration point where applicable.
- Properties for binding, substitution, arity, precedence, and parse/render round trips.
- Updated README scope, changelog/release notes, and CI coverage.

No stage is complete when it merely compiles or accepts one example.

## Quality-assurance gates

Every pull request must pass:

1. `lake build` for all libraries, examples, tests, and properties.
2. Unit tests for successful parses, malformed input, comments, Unicode, and error positions.
3. Official fixture tests and the pinned corpus regression job.
4. Parse/render/parse properties wherever canonical rendering is supported.
5. Independent differential checks against the TPTP ANTLR grammar or another parser for
   accepted/rejected syntax and selected structural facts.
6. Scope, arity, declaration-order, and type checks for the validation layer.
7. Axiom, total-parser, style, formatting, and documentation checks.
8. OATP integration tests for any API consumed outside `lean-tptp`.

The release checklist additionally requires a clean worktree, a pinned dependency/corpus
revision, a tagged version, and a green remote CI run. Unsupported constructs must produce a
clear error or remain available through the raw envelope; they must never be silently dropped.

## P0 — complete FOF and CNF

Difficulty: medium-high. Verification confidence: high after official fixtures, a curated
TPTP corpus, and negative/differential tests. `prop-pack` remains useful for propositional
smoke tests, but it is not evidence of general FOF/CNF coverage.

### P0.1 Freeze the compatibility boundary

- [ ] Keep `TPTP.parse` and `TPTP.Statement` lossless and source-compatible.
- [ ] Add `TPTP.FOF` and `TPTP.CNF` modules rather than making the current small
  `TPTP.Formula` AST silently change meaning.
- [ ] Reuse shared names, tokens, comments, spans, and Grip error formatting; do not create
  separate lexers for FOF and CNF.
- [ ] Record the exact TPTP grammar revision being implemented and list unsupported future
  productions explicitly.

### P0.2 Build the shared lexical layer

- [ ] Parse lower-word, upper-word, quoted-word, back-quoted word, `$`-defined symbols,
  system symbols, unsigned/signed integer, rational, and real tokens as required by the
  selected FOF/CNF grammar.
- [ ] Handle escaped quotes/backslashes, comments, whitespace, Unicode source positions,
  and all multi-character operators before single-character alternatives.
- [ ] Preserve token spans so formula errors point at the actual operator, name, or term.
- [ ] Add lexer tests for every token family and every ambiguous prefix (`<=>`, `=>`, `<=`,
  `<~>`, `~|`, `~&`, `!=`, and `=`).

### P0.3 Define shared terms and FOF formulas

- [ ] Replace string-only semantic terms with a shared AST for variables, constants,
  function applications, defined terms, and system terms while retaining original source
  text at the statement boundary.
- [ ] Add atoms for propositions, predicates, equality, inequality, defined predicates,
  and system atoms.
- [ ] Add `$true`, `$false`, unary negation, `!`/`?` quantifiers, conjunction, disjunction,
  and all FOF non-associative connectives from the reference grammar.
- [ ] Represent associative `&` and `|` without inventing precedence for unrelated binary
  connectives: FOF has no general precedence among binary connectives, and parentheses are
  required where the grammar requires them.
- [ ] Represent binder scope explicitly; do not treat uppercase-looking names as bound just
  because they lex as variables.

### P0.4 Implement the FOF parser

- [ ] Implement the reference grammar with Grip's total `fix`, using explicit grammar
  layers for unitary, unary, associative, and non-associative formulas.
- [ ] Parse nested function arguments and recursive terms without falling back to raw text.
- [ ] Reject chained non-associative connectives and malformed binder scope at the correct
  byte position.
- [ ] Add `parse`, `parseString`, and statement helpers that verify the statement kind is
  `fof` before returning a typed formula.
- [ ] Keep syntax parsing separate from well-formedness validation: unbound variables,
  declaration assumptions, and symbol interpretation belong in validation.

### P0.5 Define and implement CNF

- [ ] Define `CNF.Literal` and `CNF.Clause` as a clause/disjunction model, reusing FOF
  atomic terms and equality rather than duplicating them.
- [ ] Parse only CNF literals: positive/negative atoms, equality/inequality, and the
  allowed defined/system atomic forms.
- [ ] Enforce that CNF formulas contain no FOF quantifiers or arbitrary binary connectives.
- [ ] Document and test that CNF variables are implicitly universally quantified.
- [ ] Add empty/singleton/nested-parenthesized clauses and malformed literal fixtures.
- [ ] Add `parseCNF` and `Statement.parseCNF` helpers that reject non-`cnf` statements.

### P0.6 Canonical rendering and validation

- [ ] Add a canonical FOF renderer only after the AST has explicit grouping information;
  use full parentheses when that avoids relying on unspecified precedence.
- [ ] Add a canonical CNF renderer with stable literal/clause grouping.
- [ ] Add validation for variable binding, legal CNF shape, and optional symbol arity
  environments without pretending to perform type checking.
- [ ] Prove or test alpha-renaming and parse/render/parse equivalence for formulas with
  nested binders.
- [ ] Keep unsupported/system-specific constructs lossless at the envelope level.

### P0.7 Corpus and differential verification

- [ ] Add official sample fixtures such as the TPTP CNF and FOF examples, plus hand-written
  fixtures covering every production family.
- [ ] Add a curated, pinned FOF/CNF subset from the TPTP Problem Library; do not download
  the full multi-gigabyte library in ordinary CI.
- [ ] Keep the pinned `prop-pack` corpus as the fast propositional regression suite.
- [ ] Compare accepted/rejected cases and selected AST facts against the official ANTLR
  grammar or `tptp4X`; never use only the new renderer as its own oracle.
- [ ] Record file, statement, and dialect counts in CI and retain failing corpus paths.

### P0 exit criterion

FOF and CNF statements parse into typed ASTs with no fallback for the selected grammar
revision; malformed and semantically invalid fixtures fail in the correct layer; the
curated TPTP subset passes; normalized output parses back to an equivalent AST; and OATP
can consume the typed result without touching the raw envelope implementation.

## P1 — monomorphic typed first-order form (TFF0)

Difficulty: medium-high. Verification confidence: high for syntax; separate for typing.

- [ ] Add type expressions, `$tType`, `$i`, `$o`, user-defined types, function types,
  product-style argument signatures, and typed variables.
- [ ] Parse `type` declarations and typed formulas without conflating declarations with
  ordinary formulas.
- [ ] Add typed terms, typed equality, arithmetic and standard defined symbols required by
  TFF0, while preserving unknown symbols for forward compatibility.
- [ ] Add a `validate` layer for declaration ordering, duplicate declarations, arity, and
  type compatibility; do not hide validation failures inside the syntax parser.
- [ ] Test default typing, explicit typing, ill-typed applications, arithmetic literals,
  and declaration-order errors against recorded examples.

Exit criterion: TFF0 syntax is complete for the selected reference version and the
validator reports useful errors for invalid signatures without changing parser behavior.

## P2 — polymorphic typed first-order form (TFF1)

Difficulty: high. Verification confidence: medium-high after type substitution tests.

- [ ] Add type variables and polymorphic type quantification (`!>`).
- [ ] Add polymorphic declarations and explicit type arguments at use sites.
- [ ] Model type substitution and alpha-renaming as pure operations with laws.
- [ ] Extend validation for kind/arity errors, illegal type-variable scope, and invalid
  instantiations.
- [ ] Test monomorphic cases through the polymorphic path to prevent dialect drift.

Exit criterion: TFF1 examples round-trip with stable binders, substitutions preserve
meaning, and invalid type scopes are rejected with positioned diagnostics.

## P3 — monomorphic typed higher-order form (THF0)

Difficulty: high. Verification confidence: medium; parser correctness is easier than
semantic/type correctness.

- [ ] Extend types to curried higher-order signatures.
- [ ] Add lambda terms (`^`), explicit application (`@`), higher-order variables, and
  quantification over functions and predicates.
- [ ] Add equality, choice, description, and the standard higher-order defined symbols
  required by the selected THF0 reference subset.
- [ ] Keep parsing and beta/eta/type normalization separate; do not claim a kernel or
  theorem prover in this package.
- [ ] Test precedence around application, lambda scope, nested binders, and function
  equality with golden ASTs and negative scope cases.

Exit criterion: all selected THF0 constructs have unambiguous ASTs and round-trip tests;
semantic normalization is explicitly documented as a separate concern.

## P4 — polymorphic and dependent higher-order forms (THF1/DHF0/DHF1)

Difficulty: very high. Verification confidence: medium-low until an independent oracle is
available.

- [ ] Reuse the typed core from P1–P3 for polymorphic higher-order types.
- [ ] Add dependent type binders and dependent applications only after representative
  fixtures demonstrate a real consumer need.
- [ ] Define universe/kind representation and scoping rules before adding productions.
- [ ] Add substitution, alpha-equivalence, and capture-avoidance properties before adding
  a renderer.
- [ ] Differential-test syntax against the official grammar and, where available, an
  independent TPTP parser; do not use the implementation's own renderer as the only
  oracle.

Exit criterion: the supported subset is explicitly named (for example, `DH0` rather than
“DHF”), has independent fixtures, and has a documented boundary for unsupported features.

## P5 — non-classical typed forms (NXF/NHF and later variants)

Difficulty: very high. Verification confidence: low-to-medium and logic-dependent.

- [ ] Identify the exact non-classical dialects required by OATP or another consumer.
- [ ] Add logic/profile metadata instead of baking modal or intuitionistic behavior into
  the classical AST.
- [ ] Add the corresponding connectives, annotations, and validation rules in isolated
  modules.
- [ ] Test each profile with its own positive and negative corpus; never infer support for
  all non-classical variants from one passing fixture.

Exit criterion: every advertised profile has a named grammar subset, fixtures, validation
rules, and documentation of its semantic assumptions.

## Cross-cutting TSTP work

- [ ] Parse derivation/source annotations into a structured AST after the formula AST is
  stable.
- [ ] Preserve inference rules, parent references, statuses, and useful information while
  retaining unknown annotations losslessly.
- [ ] Add real prover outputs from Vampire, E, Metis, and SystemOnTPTP as fixtures.
- [ ] Keep proof reconstruction and Lean translation in OATP or a dedicated consumer; this
  package should provide syntax and validated data, not an ATP proof engine.

## Verification hardness

The main risk is not recognizing punctuation; it is proving that the parser accepts exactly
the intended dialect and that AST transformations preserve binding and typing. Therefore the
test strategy must progress from easiest to hardest:

1. Grammar conformance: official positive and negative syntax fixtures.
2. Position accuracy: byte offsets, lines, columns, and expected-token diagnostics.
3. Structural invariants: scopes, arities, binder uniqueness, and declaration ordering.
4. Round trips: normalized parse/render/parse for ASTs with a defined canonical form.
5. Differential checks: compare accepted/rejected inputs and selected AST facts with an
   independent parser or official tools.
6. Corpus checks: pinned full files, statement counts, dialect counts, and regression cases.

Do not advance a stage because the parser builds. Advance it when its exit criterion and
verification evidence are present.
