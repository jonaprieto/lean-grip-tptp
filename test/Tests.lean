/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

open TPTP

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def documentSource : String :=
  "% a comment\n" ++
    "include('Axioms/foo.p', [a1, a2]).\n" ++
    "fof(ax, axiom, p(a)).\n" ++
    "tff(type, type, $int < $int, introduced(definition)).\n" ++
    "cnf(`Goal, conjecture, p(a) | ~q(a), inference(resolution, [status(thm)], [ax])).\n"

private def checkDocument : IO Unit := do
  let document ← match parseString documentSource with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty documentSource.toUTF8))
  check (document.items.size == 4) "document item count"
  match document.items[0]? with
  | some (Item.include value) =>
      check (value.path == .quoted "'Axioms/foo.p'") "quoted include path"
      check (value.selection == some "[a1, a2]") "include selection"
  | _ => throw (IO.userError "first item is not an include")
  match document.items[1]? with
  | some (Item.statement value) =>
      check (value.kind == .fof) "fof kind"
      check (value.role == .axiom) "axiom role"
      check (value.formula == "p(a)") "formula body"
  | _ => throw (IO.userError "second item is not a statement")
  match document.items[3]? with
  | some (Item.statement value) =>
      check (value.name == .quoted "`Goal") "back-quoted statement name"
      check (value.annotations == some "inference(resolution, [status(thm)], [ax])")
        "nested annotation split"
  | _ => throw (IO.userError "fourth item is not a statement")
  match parseStatementString "fof(datatype, type-datatype, p(a))." with
  | .ok statement => check (statement.role == .other "type-datatype") "subrole"
  | .error error =>
      throw (IO.userError (error.pretty "fof(datatype, type-datatype, p(a)).".toUTF8))

private def checkFormula : IO Unit := do
  let source := "! [X] : (p(X) => q(X))"
  let formula ← match Formula.parseFormulaString source with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty source.toUTF8))
  match formula with
  | .forall variables (.implies (.atom "p" arguments) (.atom "q" result)) =>
      check (variables.size == 1 && variables[0]? == some "X") "quantifier variables"
      check (arguments.size == 1 && result.size == 1) "atom arguments"
      match Formula.Expr.toTPTP formula with
      | .ok rendered => check (rendered == "![X] : ((p(X) => q(X)))") "formula rendering"
      | .error message => throw (IO.userError message)
  | _ => throw (IO.userError "formula AST shape")

private def checkErrors : IO Unit := do
  match parseStatementString "fof(bad, axiom, p(" with
  | .ok _ => throw (IO.userError "malformed statement accepted")
  | .error error => check (error.pos > 0) "positioned parse error"
  match Formula.parseFormulaString "p(" with
  | .ok _ => throw (IO.userError "malformed formula accepted")
  | .error _ => pure ()

private def checkComments : IO Unit := do
  let source := "fof(line, axiom, p(a) % ) , ignored\n, inference(foo, [status(thm)]))."
  let block := "fof(block, axiom, p(a) /* ) , ignored */ , inference(foo, [status(thm)]))."
  for input in [source, block] do
    match parseStatementString input with
    | .ok statement =>
        check (statement.annotations == some "inference(foo, [status(thm)])")
          "comment-aware annotation split"
    | .error error => throw (IO.userError (error.pretty input.toUTF8))

private def checkFOF : IO Unit := do
  let source := "! [X] : (p(X) => q(X))"
  let formula ← match FOF.parseFormulaString source with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty source.toUTF8))
  let expected : FOF.Formula :=
    .forall #["X"] (.implies
      (.atom (.predicate { raw := "p" } #[.variable "X"]))
      (.atom (.predicate { raw := "q" } #[.variable "X"])))
  check (formula == expected) "complete FOF formula shape"
  match FOF.validate formula with
  | .ok () => pure ()
  | .error error => throw (IO.userError s!"bound FOF rejected: {error}")
  let rendered := formula.render
  check (rendered == "! [X] : ((p(X) => q(X)))") "canonical FOF rendering"
  match FOF.parseFormulaString rendered with
  | .ok reparsed => check (reparsed == formula) "FOF parse/render/parse"
  | .error error => throw (IO.userError (error.pretty rendered.toUTF8))
  for input in [
      "p & q & r", "p | q | r", "p <=> q", "p => q", "p <= q", "p <~> q",
      "p ~| q", "p ~& q", "a = b", "a != b", "p(\"x\")", "p('quoted')",
      "p(`X)", "p(-1, 1/2, 1.5, 1E2, 1.5E-2)", "$distinct(a, b)", "$$tool(a)",
      "$quotient_e(a, b)"
    ] do
    match FOF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error =>
        throw (IO.userError (s!"FOF rejected `{input}`:\n{error.pretty input.toUTF8}"))
  let statement : Statement :=
    { kind := .fof, name := .bare "goal", role := .conjecture, formula := source }
  match FOF.parseStatementFormula statement with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "FOF statement formula rejected")
  let wrongKind : Statement := { statement with kind := .cnf }
  match FOF.parseStatementFormula wrongKind with
  | .error (.wrongKind .fof .cnf) => pure ()
  | _ => throw (IO.userError "FOF accepted a CNF statement")
  match FOF.parseFormulaString "p => q & r" with
  | .ok _ => throw (IO.userError "FOF accepted mixed unparenthesized connectives")
  | .error _ => pure ()
  match FOF.parseFormulaString "p(" with
  | .ok _ => throw (IO.userError "FOF accepted malformed term")
  | .error _ => pure ()
  for input in ["1", "\"object\""] do
    match FOF.parseFormulaString input with
    | .ok _ => throw (IO.userError s!"FOF accepted invalid proposition `{input}`")
    | .error _ => pure ()
  let unbound : FOF.Formula :=
    .atom (.predicate { raw := "p" } #[.variable "X"])
  match FOF.validate unbound with
  | .error (.unboundVariable "X") => pure ()
  | _ => throw (IO.userError "FOF accepted an unbound variable")
  let duplicate : FOF.Formula := .forall #["X", "X"] .truth
  match FOF.validate duplicate with
  | .error (.duplicateBinder "X") => pure ()
  | _ => throw (IO.userError "FOF accepted a duplicate binder")
  let empty : FOF.Formula := .forall #[] .truth
  match FOF.validate empty with
  | .error .emptyBinder => pure ()
  | _ => throw (IO.userError "FOF accepted an empty binder")
  let unknown : FOF.Formula := .atom (.predicate { raw := "$mystery" } #[])
  match FOF.validate unknown with
  | .error (.unknownDefinedSymbol "$mystery") => pure ()
  | _ => throw (IO.userError "FOF accepted an unknown defined symbol")
  let missingArguments : FOF.Formula := .atom (.predicate { raw := "$less" } #[])
  match FOF.validate missingArguments with
  | .error (.invalidDefinedArity "$less" 0) => pure ()
  | _ => throw (IO.userError "FOF accepted a defined predicate without arguments")

private def checkCNF : IO Unit := do
  let source := "(p(a) | ~q(a) | r(a) != s(a))"
  let clause ← match CNF.parseFormulaString source with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty source.toUTF8))
  check (clause.literals.size == 3) "CNF literal count"
  for input in ["p(a) | ~(q(a)) | r(a) != s(a)", "((p(a) | ~q(a)) )"] do
    match CNF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error =>
        throw (IO.userError (s!"CNF regression `{input}`:\n{error.pretty input.toUTF8}"))
  match clause.literals[1]? with
  | some (CNF.Literal.negative (FirstOrder.Atom.predicate symbol _)) =>
      check (symbol.raw == "q") "CNF negative literal"
  | _ => throw (IO.userError "CNF negative literal shape")
  match clause.literals[2]? with
  | some (CNF.Literal.positive (FirstOrder.Atom.inequality _ _)) => pure ()
  | _ => throw (IO.userError "CNF inequality literal shape")
  let rendered := clause.render
  check (rendered == "p(a) | ~(q(a)) | r(a) != s(a)") "canonical CNF rendering"
  match CNF.parseFormulaString rendered with
  | .ok reparsed => check (reparsed == clause) "CNF parse/render/parse"
  | .error error => throw (IO.userError (error.pretty rendered.toUTF8))
  let empty ← match CNF.parseFormulaString "$false" with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty "$false".toUTF8))
  check empty.literals.isEmpty "CNF empty clause"
  check (empty.render == "$false") "CNF empty clause rendering"
  for input in [
      "$true", "$distinct(a, b)", "$$system(a)", "1 != 2", "\"a\" != \"b\"",
      "~($less(a, b))"
    ] do
    match CNF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error =>
        throw (IO.userError (s!"CNF rejected `{input}`:\n{error.pretty input.toUTF8}"))
  let statement : Statement :=
    { kind := .cnf, name := .bare "goal", role := .conjecture, formula := source }
  match CNF.parseStatementFormula statement with
  | .ok value => check (value == clause) "CNF statement formula"
  | .error _ => throw (IO.userError "CNF statement formula rejected")
  for input in ["p => q", "![X] : p(X)", "()"] do
    match CNF.parseFormulaString input with
    | .ok _ => throw (IO.userError s!"CNF accepted `{input}`")
    | .error _ => pure ()
  for input in ["p & q | r", "p | q & r", "p => q => r", "p |", "~ ~p"] do
    match CNF.parseFormulaString input with
    | .ok _ => throw (IO.userError s!"CNF accepted `{input}`")
    | .error _ => pure ()

private def checkTFF : IO Unit := do
  let source := [
    "tff(human_type,type,human: $tType).",
    "tff(grade_type,type,grade: $tType).",
    "tff(john_decl,type,john: human).",
    "tff(a_decl,type,a: grade).",
    "tff(f_decl,type,f: grade).",
    "tff(grade_of_decl,type,grade_of: human > grade).",
    "tff(created_equal_decl,type,created_equal: (human * human) > $o).",
    "tff(all_created_equal,axiom,![H1:human,H2:human]:created_equal(H1,H2)).",
    "tff(john_got_an_f,axiom,grade_of(john) = f).",
    "tff(someone_got_an_a,conjecture,?[H:human]:grade_of(H) = a).",
    "tff(arithmetic,axiom,![X:$int,Y:$int]:$less(X,$sum(Y,1)))."
  ]
  let mut bodies : Array TFF.Body := #[]
  for line in source do
    let statement ← match parseStatementString line with
      | .ok value => pure value
      | .error error => throw (IO.userError (error.pretty line.toUTF8))
    let body ← match TFF.parseStatementBody statement with
      | .ok value => pure value
      | .error (.syntax error) => throw (IO.userError (error.pretty statement.formula.toUTF8))
      | .error (.wrongKind expected actual) =>
          throw (IO.userError s!"kind error: {expected} vs {actual}")
    bodies := bodies.push body
  let signature ← match TFF.validateDocument bodies with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"TFF validation: {error}")
  check (signature.declarations.size == 7) "TFF declaration/default count"
  let formulaSource := "![X:$real,Y:$real] : ($greater(X,Y) => X != Y)"
  let formula ← match TFF.parseFormulaString formulaSource with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty formulaSource.toUTF8))
  let rendered := formula.render
  match TFF.parseFormulaString rendered with
  | .ok reparsed => check (reparsed == formula) "TFF parse/render/parse"
  | .error error => throw (IO.userError (error.pretty rendered.toUTF8))
  let declaration ← match TFF.parseTypeDeclarationString "owns: (human * cat) > $o" with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty "owns: (human * cat) > $o".toUTF8))
  let declarationRendered := declaration.render
  match TFF.parseTypeDeclarationString declarationRendered with
  | .ok reparsed => check (reparsed == declaration) "TFF declaration parse/render/parse"
  | .error error => throw (IO.userError (error.pretty declarationRendered.toUTF8))
  for input in [
      "![X:human] : p(X)", "p(1) = $sum(1, 2)", "$distinct(1, 2)",
      "![X] : p(X)", "p(a) | ~q(a)", "p != q", "p ~| q", "p ~& q"
    ] do
    match TFF.parseFormulaString input with
    | .ok _ => pure ()
    | .error error => throw (IO.userError (s!"TFF rejected {input}:\n{error.pretty input.toUTF8}"))
  match TFF.parseFormulaString "![X] : p(X)" with
  | .ok formula =>
      let signature : TFF.Signature := { declarations := #[
        { symbol := { raw := "human" }, type := .atom { raw := "$tType" } }] }
      match TFF.validateFormula signature formula with
      | .ok _ => pure ()
      | .error error => throw (IO.userError s!"TFF default typing: {error}")
  | .error error => throw (IO.userError (error.pretty "![X:human] : p(X)".toUTF8))
  match TFF.parseFormulaString "![X:human] : p(X)" with
  | .ok formula =>
      let signature : TFF.Signature := { declarations := #[
        { symbol := { raw := "human" }, type := .atom { raw := "$tType" } },
        { symbol := { raw := "grade" }, type := .atom { raw := "$tType" } },
        { symbol := { raw := "p" },
          type := .mapping #[.atom { raw := "grade" }] (.atom { raw := "$o" }) }
      ] }
      match TFF.validateFormula signature formula with
      | .ok _ => throw (IO.userError "TFF accepted a formula with an unknown type")
      | .error _ => pure ()
  | .error error => throw (IO.userError (error.pretty "![X:human] : p(X)".toUTF8))
  let polymorphicSource := [
    "tff(bird_type,type,bird: $tType).",
    "tff(list_type,type,list: $tType > $tType).",
    "tff(map_type,type,map: ($tType * $tType) > $tType).",
    "tff(is_empty_type,type,is_empty: !>[A:$tType] : (list(A) > $o)).",
    "tff(cons_type,type,cons: !>[A:$tType] : ((A * list(A)) > list(A))).",
    "tff(nil_type,type,nil: !>[A:$tType] : list(A)).",
    "tff(identity_type,type,identity: !>[A:$tType] : (A > A)).",
    "tff(lookup_type,type,lookup: !>[A:$tType,B:$tType] : ((map(A,B) * A) > B))."
  ]
  let mut polymorphicBodies : Array TFF.Body := #[]
  for line in polymorphicSource do
    let statement ← match parseStatementString line with
      | .ok value => pure value
      | .error error => throw (IO.userError (error.pretty line.toUTF8))
    let body ← match TFF.parseStatementBody statement with
      | .ok value => pure value
      | .error (.syntax error) =>
          throw (IO.userError (error.pretty statement.formula.toUTF8))
      | .error (.wrongKind expected actual) =>
          throw (IO.userError s!"kind error: {expected} vs {actual}")
    polymorphicBodies := polymorphicBodies.push body
  let polymorphicSignature ← match TFF.validateDocument polymorphicBodies with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"TF1 validation: {error}")
  check (polymorphicSignature.declarations.size == 8) "TF1 declaration count"
  let polymorphicFormula := "![A:$tType,X:A,Xs:list(A)] : is_empty(A,cons(A,X,Xs))"
  let formula ← match TFF.parseFormulaString polymorphicFormula with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty polymorphicFormula.toUTF8))
  match TFF.validateFormula polymorphicSignature formula with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"TF1 formula validation: {error}")
  let renderedPolymorphic := formula.render
  match TFF.parseFormulaString renderedPolymorphic with
  | .ok reparsed => check (reparsed == formula) "TF1 formula parse/render/parse"
  | .error error => throw (IO.userError (error.pretty renderedPolymorphic.toUTF8))
  let polymorphicDeclaration ← match
      TFF.parseTypeDeclarationString "nil: !>[A:$tType] : list(A)" with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty "nil: !>[A:$tType] : list(A)".toUTF8))
  let renderedDeclaration := polymorphicDeclaration.render
  match TFF.parseTypeDeclarationString renderedDeclaration with
  | .ok reparsed => check (reparsed == polymorphicDeclaration) "TF1 declaration parse/render/parse"
  | .error error => throw (IO.userError (error.pretty renderedDeclaration.toUTF8))
  let identityFormula := "![A:$tType,X:A] : identity(A,X) = X"
  let identity ← match TFF.parseFormulaString identityFormula with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty identityFormula.toUTF8))
  match TFF.validateFormula polymorphicSignature identity with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"TF1 identity validation: {error}")
  let lookupFormula :=
    "![A:$tType,B:$tType,M:map(A,B),K:A,V:B] : lookup(A,B,M,K) = V"
  let lookup ← match TFF.parseFormulaString lookupFormula with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty lookupFormula.toUTF8))
  match TFF.validateFormula polymorphicSignature lookup with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"TF1 lookup validation: {error}")
  let identityRendered := identity.render
  match TFF.parseFormulaString identityRendered with
  | .ok reparsed => check (reparsed == identity) "TF1 formula render/parse"
  | .error error => throw (IO.userError (error.pretty identityRendered.toUTF8))
  let polymorphicDeclaration ← match TFF.parseTypeDeclarationString
      "identity: !>[A:$tType] : (A > A)" with
    | .ok value => pure value
    | .error error => throw (IO.userError (error.pretty "identity: !>[A:$tType] : (A > A)".toUTF8))
  match TFF.parseTypeDeclarationString polymorphicDeclaration.render with
  | .ok reparsed => check (reparsed == polymorphicDeclaration) "TF1 declaration render/parse"
  | .error error => throw (IO.userError (error.pretty polymorphicDeclaration.render.toUTF8))
  for (label, source) in [
      ("missing type argument", "![X:$int] : identity(X) = X"),
      ("wrong type argument", "identity($o, $true) = $true"),
      ("unknown type argument", "identity(unknown, a) = a"),
      ("wrong constructor arity", "![A:$tType,X:A] : is_empty(list(A), X)"),
      ("type variable as term", "![A:$tType] : identity(A, A) = A")
    ] do
    match TFF.parseFormulaString source with
    | .ok value =>
        match TFF.validateFormula polymorphicSignature value with
        | .ok _ => throw (IO.userError s!"TF1 accepted {label}: {source}")
        | .error _ => pure ()
    | .error _ => pure ()
  let substituted := (TFF.TypeExpr.application { raw := "list" } #[.atom { raw := "A" }]).substitute
    #[("A", .atom { raw := "$int" })]
  check (substituted == .application { raw := "list" } #[.atom { raw := "$int" }])
    "TF1 type substitution"
  let quantified : TFF.TypeExpr := .forall #[{ name := "B" }]
    (.application { raw := "list" } #[.atom { raw := "A" }, .atom { raw := "B" }])
  let captured := quantified.substitute #[("A", .atom { raw := "B" })]
  let expectedCaptured : TFF.TypeExpr := .forall #[{ name := "B_1" }]
    (.application { raw := "list" } #[.atom { raw := "B" }, .atom { raw := "B_1" }])
  check (captured == expectedCaptured) "TF1 capture-avoiding substitution"
  check (quantified.freeVariables == #["A"]) "TF1 free type variables"
  let renamed := quantified.alphaRename "B" "C"
  let expectedRenamed : TFF.TypeExpr := .forall #[{ name := "C" }]
    (.application { raw := "list" } #[.atom { raw := "A" }, .atom { raw := "C" }])
  check (renamed == expectedRenamed) "TF1 alpha renaming"
  let renamed := (TFF.TypeExpr.forall #[{ name := "A" }]
      (.application { raw := "list" } #[.atom { raw := "A" }])).alphaRename "A" "B"
  check (renamed == .forall #[{ name := "B" }]
      (.application { raw := "list" } #[.atom { raw := "B" }])) "TF1 alpha renaming"

def main : IO Unit := do
  checkDocument
  checkFormula
  checkErrors
  checkComments
  checkFOF
  checkCNF
  checkTFF
  IO.println "TPTP tests: ok"
