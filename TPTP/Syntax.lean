import Grip

/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

/-!
# TPTP.Syntax: format-neutral TPTP and TSTP values

The envelope types preserve syntax that this library does not interpret yet.
That keeps parsing useful for every prover while the optional first-order
formula parser can provide structure for the supported `fof`/`cnf` fragment.
-/

namespace TPTP

inductive Name where
  /-- An unquoted TPTP name. -/
  | bare (value : String)
  /-- A quoted TPTP name, including its original quote and escape spelling. -/
  | quoted (raw : String)
  deriving BEq, DecidableEq, Repr

def Name.render : Name → String
  | .bare value => value
  | .quoted raw => raw

instance : ToString Name where
  toString := Name.render

inductive Kind where
  | fof
  | cnf
  | tff
  | thf
  | tcf
  | tpi
  | other (value : String)
  deriving BEq, DecidableEq, Repr

def Kind.ofString : String → Kind
  | "fof" => .fof
  | "cnf" => .cnf
  | "tff" => .tff
  | "thf" => .thf
  | "tcf" => .tcf
  | "tpi" => .tpi
  | value => .other value

def Kind.render : Kind → String
  | .fof => "fof"
  | .cnf => "cnf"
  | .tff => "tff"
  | .thf => "thf"
  | .tcf => "tcf"
  | .tpi => "tpi"
  | .other value => value

instance : ToString Kind where
  toString := Kind.render

inductive Role where
  | axiom
  | hypothesis
  | definition
  | assumption
  | lemma
  | theorem
  | corollary
  | conjecture
  | negatedConjecture
  | plain
  | type
  | interpretation
  | logic
  | unknown
  | finiteDomain
  | finiteFunctor
  | finitePredicate
  | other (value : String)
  deriving BEq, DecidableEq, Repr

def Role.ofString : String → Role
  | "axiom" => .axiom
  | "hypothesis" => .hypothesis
  | "definition" => .definition
  | "assumption" => .assumption
  | "lemma" => .lemma
  | "theorem" => .theorem
  | "corollary" => .corollary
  | "conjecture" => .conjecture
  | "negated_conjecture" => .negatedConjecture
  | "plain" => .plain
  | "type" => .type
  | "interpretation" => .interpretation
  | "logic" => .logic
  | "unknown" => .unknown
  | "fi_domain" => .finiteDomain
  | "fi_functors" => .finiteFunctor
  | "fi_predicates" => .finitePredicate
  | value => .other value

def Role.render : Role → String
  | .axiom => "axiom"
  | .hypothesis => "hypothesis"
  | .definition => "definition"
  | .assumption => "assumption"
  | .lemma => "lemma"
  | .theorem => "theorem"
  | .corollary => "corollary"
  | .conjecture => "conjecture"
  | .negatedConjecture => "negated_conjecture"
  | .plain => "plain"
  | .type => "type"
  | .interpretation => "interpretation"
  | .logic => "logic"
  | .unknown => "unknown"
  | .finiteDomain => "fi_domain"
  | .finiteFunctor => "fi_functors"
  | .finitePredicate => "fi_predicates"
  | .other value => value

instance : ToString Role where
  toString := Role.render

/-- A parsed `fof`, `cnf`, `tff`, `thf`, `tcf`, or `tpi` statement. -/
structure Statement where
  kind : Kind
  name : Name
  role : Role
  /-- The formula/type body, preserved as source text. -/
  formula : String
  /-- The optional TSTP annotation after the formula. -/
  annotations : Option String := none
  deriving BEq, DecidableEq, Repr

inductive FormulaError where
  | syntax (error : Grip.ParseError)
  | wrongKind (expected actual : Kind)
  deriving BEq, Repr

/-- An `include(...)` directive. -/
structure Include where
  path : Name
  selection : Option String := none
  deriving BEq, DecidableEq, Repr

inductive Item where
  | statement (value : Statement)
  | include (value : Include)
  deriving BEq, DecidableEq, Repr

/-- A TPTP/TSTP source containing statements and include directives in order. -/
structure Document where
  items : Array Item
  deriving BEq, DecidableEq, Repr

namespace Formula

inductive Term where
  | var (name : String)
  | constant (name : String)
  | function (name : String) (arguments : Array Term)

inductive Expr where
  | atom (predicate : String) (arguments : Array Term)
  | truth
  | falsity
  | not (body : Expr)
  | and (left right : Expr)
  | or (left right : Expr)
  | implies (left right : Expr)
  | iff (left right : Expr)
  | forall (variables : Array String) (body : Expr)
  | exists (variables : Array String) (body : Expr)

private def join (values : List String) : String :=
  String.intercalate ", " values

private def validName (first : Char → Bool) (name : String) : Bool :=
  match name.toList with
  | [] => false
  | character :: rest => first character && rest.all (fun value =>
      Char.isAlphanum value || value == '_' || value == '$')

private def symbolName (kind name : String) : Except String String :=
  if validName (fun character => character.isLower || character == '$') name then
    .ok name
  else
    .error s!"invalid TPTP {kind} `{name}`"

private def variableName (name : String) : Except String String :=
  if validName (fun character => character.isUpper || character == '_') name then
    .ok name
  else
    .error s!"invalid TPTP variable `{name}`"

private theorem sizeOf_lt_of_mem_array {α : Type} [SizeOf α] {value : α}
    {values : Array α} (h : value ∈ values) : sizeOf value < sizeOf values := by
  exact Array.sizeOf_lt_of_mem h

def Term.toTPTP (term : Term) (bound : Array String := #[]) :
    Except String String :=
  match term with
  | .var name =>
      if bound.toList.contains name then
        .ok name
      else
        .error s!"unbound TPTP variable `{name}`"
  | .constant name => symbolName "symbol" name
  | .function name arguments => do
      let name ← symbolName "function" name
      let arguments ← arguments.toList.mapM (fun term => term.toTPTP bound)
      if arguments.isEmpty then
        pure name
      else
        pure s!"{name}({join arguments})"
termination_by sizeOf term
decreasing_by
  simp_wf
  apply Nat.lt_of_lt_of_le
    (sizeOf_lt_of_mem_array (by
      apply Array.mem_def.mpr
      assumption)) ?_
  simp +arith

private def exprDepth : Expr → Nat
  | .atom _ _ | .truth | .falsity => 0
  | .not body => exprDepth body + 1
  | .and left right
  | .or left right
  | .implies left right
  | .iff left right => max (exprDepth left) (exprDepth right) + 1
  | .forall _ body | .exists _ body => exprDepth body + 1

def Expr.toTPTP (formula : Expr) (bound : Array String := #[]) :
    Except String String :=
  match formula with
  | .atom predicate arguments => do
      let predicate ← symbolName "predicate" predicate
      let arguments ← arguments.toList.mapM (fun term => term.toTPTP bound)
      if arguments.isEmpty then
        pure predicate
      else
        pure s!"{predicate}({join arguments})"
  | .truth => pure "$true"
  | .falsity => pure "$false"
  | .not body => do
      let body ← body.toTPTP bound
      pure s!"~({body})"
  | .and left right => do
      let left ← left.toTPTP bound
      let right ← right.toTPTP bound
      pure s!"({left} & {right})"
  | .or left right => do
      let left ← left.toTPTP bound
      let right ← right.toTPTP bound
      pure s!"({left} | {right})"
  | .implies left right => do
      let left ← left.toTPTP bound
      let right ← right.toTPTP bound
      pure s!"({left} => {right})"
  | .iff left right => do
      let left ← left.toTPTP bound
      let right ← right.toTPTP bound
      pure s!"({left} <=> {right})"
  | .forall variables body => do
      let variables ← variables.toList.mapM variableName
      let body ← body.toTPTP (bound ++ variables.toArray)
      pure s!"![{join variables}] : ({body})"
  | .exists variables body => do
      let variables ← variables.toList.mapM variableName
      let body ← body.toTPTP (bound ++ variables.toArray)
      pure s!"?[{join variables}] : ({body})"
termination_by exprDepth formula
decreasing_by
  simp_wf
  all_goals simp_all [exprDepth]
  all_goals omega

end Formula

end TPTP
