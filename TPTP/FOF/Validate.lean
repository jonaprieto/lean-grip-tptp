/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FOF

/-!
# TPTP.FOF.Validate: first-order binding validation

Parsing establishes syntax. This module checks the FOF rule that every variable occurrence
must be in the scope of a quantifier; CNF variables are implicitly universally quantified.
-/

namespace TPTP.FOF

inductive ValidationError where
  | unboundVariable (name : String)
  | emptyBinder
  | duplicateBinder (name : String)
  | unknownDefinedSymbol (name : String)
  | invalidDefinedUse (name : String)
  deriving BEq, Repr

def ValidationError.message : ValidationError → String
  | .unboundVariable name => s!"unbound variable `{name}`"
  | .emptyBinder => "quantifier variable list cannot be empty"
  | .duplicateBinder name => s!"duplicate bound variable `{name}`"
  | .unknownDefinedSymbol name => s!"unknown TPTP defined symbol `{name}`"
  | .invalidDefinedUse name => s!"invalid use of TPTP defined symbol `{name}`"

instance : ToString ValidationError where
  toString := ValidationError.message

private def firstDuplicate : List String → Option String
  | [] => none
  | name :: rest => if rest.contains name then some name else firstDuplicate rest

private def definedPredicates : List String :=
  [ "$distinct", "$less", "$lesseq", "$greater", "$greatereq", "$is_int", "$is_rat" ]

private def definedTerms : List String :=
  [ "$uminus", "$sum", "$difference", "$product", "$quotient", "$quotient_e"
  , "$quotient_t", "$quotient_f", "$remainder_e", "$remainder_t", "$remainder_f"
  , "$floor", "$ceiling", "$truncate", "$round", "$to_int", "$to_rat", "$to_real" ]

private def symbolClass (name : String) : Option Bool :=
  match name.toList with
  | '$' :: '$' :: _ => some true
  | '$' :: _ => some false
  | _ => none

private def validateTermSymbol (symbol : FirstOrder.Symbol) : Except ValidationError Unit :=
  match symbolClass symbol.raw with
  | none | some true => .ok ()
  | some false =>
      if definedTerms.contains symbol.raw then .ok ()
      else .error (.unknownDefinedSymbol symbol.raw)

private def validatePredicateSymbol (symbol : FirstOrder.Symbol)
    (arguments : Array FirstOrder.Term) : Except ValidationError Unit :=
  match symbolClass symbol.raw with
  | none | some true => .ok ()
  | some false =>
      if symbol.raw == "$true" || symbol.raw == "$false" then
        if arguments.isEmpty then .ok () else .error (.invalidDefinedUse symbol.raw)
      else if definedPredicates.contains symbol.raw then
        if arguments.isEmpty then .error (.invalidDefinedUse symbol.raw) else .ok ()
      else if definedTerms.contains symbol.raw then
        .error (.invalidDefinedUse symbol.raw)
      else
        .error (.unknownDefinedSymbol symbol.raw)

private partial def validateTerm (bound : List String) :
    FirstOrder.Term → Except ValidationError Unit
  | .variable name =>
      if bound.contains name then .ok () else .error (.unboundVariable name)
  | .constant symbol => validateTermSymbol symbol
  | .function symbol arguments => do
      let _ ← validateTermSymbol symbol
      let _ ← arguments.toList.mapM (validateTerm bound)
      pure ()

private def validateAtom (bound : List String) : FirstOrder.Atom → Except ValidationError Unit
  | .predicate symbol arguments => do
      let _ ← validatePredicateSymbol symbol arguments
      let _ ← arguments.toList.mapM (validateTerm bound)
      pure ()
  | .equality left right | .inequality left right => do
      let _ ← validateTerm bound left
      validateTerm bound right

private partial def validateFormula (bound : List String) : Formula → Except ValidationError Unit
  | .atom value => validateAtom bound value
  | .truth | .falsity => .ok ()
  | .not body => validateFormula bound body
  | .and left right
  | .or left right
  | .implies left right
  | .impliedBy left right
  | .iff left right
  | .xor left right
  | .nor left right
  | .nand left right => do
      let _ ← validateFormula bound left
      validateFormula bound right
  | .forall variables body | .exists variables body =>
      if variables.isEmpty then
        .error .emptyBinder
      else
        match firstDuplicate variables.toList with
        | some name => .error (.duplicateBinder name)
        | none => validateFormula (bound ++ variables.toList) body

def validate (formula : Formula) : Except ValidationError Unit :=
  validateFormula [] formula

end TPTP.FOF
