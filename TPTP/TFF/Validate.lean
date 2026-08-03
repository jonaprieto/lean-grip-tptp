/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.TFF.Render

/-!
# TPTP.TFF.Validate: TF0 signatures and type checking

Validation is intentionally an explicit pass. TFF permits default typing for
undeclared symbols, but a later declaration must agree with that inferred
signature; validateFormula returns the updated signature for that reason.
-/

namespace TPTP.TFF

inductive ValidationError where
  | unboundVariable (name : String)
  | emptyBinder
  | duplicateBinder (name : String)
  | unknownType (name : String)
  | invalidType (message : String)
  | conflictingDeclaration (name : String) (previous : TypeExpr) (current : TypeExpr)
  | invalidArity (name : String) (expected actual : Nat)
  | invalidApplication (name : String)
  | invalidDefinedUse (name : String)
  | invalidDefinedArity (name : String) (actual : Nat)
  | typeMismatch (context : String) (expected actual : TypeExpr)
  deriving BEq, Repr, Nonempty

instance : Inhabited TypeExpr := ⟨.atom { raw := "$i" }⟩

def ValidationError.message : ValidationError → String
  | .unboundVariable name => s!"unbound variable {name}"
  | .emptyBinder => "quantifier variable list cannot be empty"
  | .duplicateBinder name => s!"duplicate bound variable {name}"
  | .unknownType name => s!"unknown TFF type {name}"
  | .invalidType message => s!"invalid TFF type: {message}"
  | .conflictingDeclaration name previous current =>
      s!"conflicting declaration for {name}: {previous} versus {current}"
  | .invalidArity name expected actual =>
      s!"invalid arity {actual} for {name}; expected {expected}"
  | .invalidApplication name => s!"invalid application of {name}"
  | .invalidDefinedUse name => s!"invalid use of TFF defined symbol {name}"
  | .invalidDefinedArity name actual =>
      s!"invalid arity {actual} for TFF defined symbol {name}"
  | .typeMismatch context expected actual =>
      s!"type mismatch in {context}: expected {expected}, found {actual}"

instance : ToString ValidationError where
  toString := ValidationError.message

structure Signature where
  declarations : Array Declaration := #[]
  deriving BEq, Repr

instance : Inhabited Signature := ⟨{}⟩

private def lookup (signature : Signature) (name : String) : Option Declaration :=
  signature.declarations.find? (fun declaration => declaration.symbol.raw == name)

private def add (signature : Signature) (declaration : Declaration) :
    Except ValidationError Signature :=
  match lookup signature declaration.symbol.raw with
  | none => .ok { declarations := signature.declarations.push declaration }
  | some previous =>
      if previous.type == declaration.type then
        .ok signature
      else
        .error (.conflictingDeclaration declaration.symbol.raw previous.type declaration.type)

private def atom (name : String) : TypeExpr :=
  .atom { raw := name }

private def isBuiltinType (name : String) : Bool :=
  ["$i", "$o", "$tType", "$int", "$rat", "$real"].contains name

private def isBoolean (type : TypeExpr) : Bool :=
  type == atom "$o"

private def isKind (type : TypeExpr) : Bool :=
  type == atom "$tType"

private def isNumeric (type : TypeExpr) : Bool :=
  ["$int", "$rat", "$real"].contains (match type with
    | .atom symbol => symbol.raw
    | _ => "")

private def typeKnown (signature : Signature) (type : TypeExpr) :
    Except ValidationError Unit :=
  match type with
  | .atom symbol =>
      if isBuiltinType symbol.raw then
        .ok ()
      else
        match lookup signature symbol.raw with
        | some declaration =>
            if declaration.type == atom "$tType" then .ok ()
            else .error (.unknownType symbol.raw)
        | none => .error (.unknownType symbol.raw)
  | .product _ | .mapping _ _ =>
      .error (.invalidType "TF0 signatures use atomic argument and result types")

private def validDeclarationName (symbol : Symbol) : Bool :=
  match symbol.raw.toList with
  | [] => false
  | '"' :: _ => false
  | '+' :: _ | '-' :: _ => false
  | first :: _ =>
      if first == '$' then
        symbol.raw.startsWith "$$"
      else
        first.isLower || first == '\'' || first == Char.ofNat 96

private def validateSignatureType (signature : Signature) (declaration : Declaration) :
    Except ValidationError Unit := do
  if !validDeclarationName declaration.symbol then
    throw (.invalidType s!"invalid declaration symbol {declaration.symbol.raw}")
  match declaration.type with
  | .atom type =>
      if type.raw == "$tType" then
        pure ()
      else
        typeKnown signature declaration.type
  | .mapping arguments result =>
      if arguments.isEmpty then
        throw (.invalidType "a function or predicate needs at least one argument")
      for argument in arguments do
        let _ ← typeKnown signature argument
        if isBoolean argument || isKind argument then
          throw (.invalidType "TFF arguments cannot have type $o or $tType")
      let _ ← typeKnown signature result
      if isKind result then
        throw (.invalidType "a TFF function or predicate cannot return $tType")
  | .product _ => throw (.invalidType "a product type must be part of a mapping")

private def definedPredicates : List String :=
  [ "$distinct", "$less", "$lesseq", "$greater", "$greatereq", "$is_int", "$is_rat" ]

private def definedTerms : List String :=
  [ "$uminus", "$sum", "$difference", "$product", "$quotient", "$quotient_e"
  , "$quotient_t", "$quotient_f", "$remainder_e", "$remainder_t", "$remainder_f"
  , "$floor", "$ceiling", "$truncate", "$round", "$abs"
  , "$to_int", "$to_rat", "$to_real" ]

private def isNumberOrDistinct (name : String) : Bool :=
  match name.toList with
  | '"' :: _ => true
  | '+' :: _ | '-' :: _ => true
  | first :: _ => first.isDigit
  | [] => false

private def literalType (name : String) : TypeExpr :=
  if name.startsWith "\"" then atom "$i"
  else if name.contains "/" then atom "$rat"
  else if name.contains "." || name.contains "e" || name.contains "E" then atom "$real"
  else atom "$int"

private def variablesLookup (variables : List (String × TypeExpr)) (name : String) :
    Option TypeExpr :=
  match variables with
  | [] => none
  | (bound, type) :: rest => if bound == name then some type else variablesLookup rest name

private def sameTypes (types : Array TypeExpr) : Option TypeExpr :=
  match types[0]? with
  | none => none
  | some first => if types.all (· == first) then some first else none

private def checkArity (name : String) (expected actual : Nat) :
    Except ValidationError Unit :=
  if expected == actual then .ok () else .error (.invalidArity name expected actual)

private def checkSame (context : String) (types : Array TypeExpr) :
    Except ValidationError TypeExpr :=
  match sameTypes types with
  | some type => .ok type
  | none =>
      match types[0]? with
      | some first =>
          match types.find? (· != first) with
          | some actual => .error (.typeMismatch context first actual)
          | none => .error (.invalidType s!"no common type in {context}")
      | none => .error (.invalidType s!"empty type list in {context}")

private def checkArguments (name : String) (expected : Array TypeExpr)
    (actual : Array TypeExpr) : Except ValidationError Unit := do
  let _ ← checkArity name expected.size actual.size
  for pair in expected.zip actual do
    let expectedType := pair.1
    let actualType := pair.2
    if expectedType != actualType then
      throw (.typeMismatch s!"argument of {name}" expectedType actualType)

private def defaultType (arity : Nat) (result : TypeExpr) : TypeExpr :=
  if arity == 0 then result else .mapping (Array.replicate arity (atom "$i")) result

private def applyDeclared (signature : Signature) (symbol : Symbol)
    (arguments : Array TypeExpr) (defaultResult : TypeExpr) :
    Except ValidationError (TypeExpr × Signature) := do
  if symbol.raw.startsWith "$" && !symbol.raw.startsWith "$$" then
    throw (.invalidDefinedUse symbol.raw)
  let (declaration, signature) ← match lookup signature symbol.raw with
    | some declaration => .ok (declaration, signature)
    | none => do
        let declaration := { symbol, type := defaultType arguments.size defaultResult }
        let signature ← add signature declaration
        pure (declaration, signature)
  match declaration.type with
  | .mapping expected result => do
      let _ ← checkArguments symbol.raw expected arguments
      pure (result, signature)
  | .atom result =>
      if arguments.isEmpty then
        pure (.atom result, signature)
      else
        throw (.invalidArity symbol.raw 0 arguments.size)
  | .product _ => throw (.invalidApplication symbol.raw)

mutual
private partial def checkTerms (signature : Signature)
    (variables : List (String × TypeExpr)) :
    List Term → Except ValidationError (Array TypeExpr × Signature)
  | [] => .ok (#[], signature)
  | term :: rest => do
      let (type, signature) ← checkTerm signature variables term
      let (types, signature) ← checkTerms signature variables rest
      pure (#[type] ++ types, signature)

private partial def definedTermType (signature : Signature) (symbol : Symbol)
    (arguments : Array TypeExpr) : Except ValidationError (TypeExpr × Signature) := do
  let name := symbol.raw
  if !definedTerms.contains name then
    throw (.invalidDefinedUse name)
  let requireNumeric := do
    let _ ← arguments.toList.mapM (fun type =>
      if isNumeric type then .ok () else .error (.typeMismatch s!"argument of {name}"
        (atom "$int") type))
    checkSame s!"arguments of {name}" arguments
  match name with
  | "$uminus" | "$floor" | "$ceiling" | "$truncate" | "$round" | "$abs" => do
      let _ ← checkArity name 1 arguments.size
      let type ← requireNumeric
      pure (type, signature)
  | "$sum" | "$difference" | "$product" | "$quotient_e" | "$quotient_t"
    | "$quotient_f" | "$remainder_e" | "$remainder_t" | "$remainder_f" => do
      let _ ← checkArity name 2 arguments.size
      let type ← requireNumeric
      pure (type, signature)
  | "$quotient" => do
      let _ ← checkArity name 2 arguments.size
      let type ← requireNumeric
      pure (if type == atom "$int" then atom "$rat" else type, signature)
  | "$to_int" => do
      let _ ← checkArity name 1 arguments.size
      let _ ← requireNumeric
      pure (atom "$int", signature)
  | "$to_rat" => do
      let _ ← checkArity name 1 arguments.size
      let _ ← requireNumeric
      pure (atom "$rat", signature)
  | "$to_real" => do
      let _ ← checkArity name 1 arguments.size
      let _ ← requireNumeric
      pure (atom "$real", signature)
  | _ => throw (.invalidDefinedUse name)

private partial def definedPredicateType (signature : Signature) (symbol : Symbol)
    (arguments : Array TypeExpr) : Except ValidationError (TypeExpr × Signature) := do
  let name := symbol.raw
  if !definedPredicates.contains name then
    throw (.invalidDefinedUse name)
  if name == "$distinct" then
    let _ ← if arguments.isEmpty then
      .error (.invalidDefinedArity name 0)
    else
      .ok ()
    let type ← checkSame s!"arguments of {name}" arguments
    if isBoolean type || isKind type then
      throw (.invalidType s!"{name} cannot compare type {type}")
    pure (atom "$o", signature)
  else if name == "$is_int" || name == "$is_rat" then
    let _ ← checkArity name 1 arguments.size
    match arguments[0]? with
    | some type =>
        if isNumeric type then pure (atom "$o", signature)
        else throw (.typeMismatch s!"argument of {name}" (atom "$int") type)
    | none => throw (.invalidDefinedArity name arguments.size)
  else
    let _ ← checkArity name 2 arguments.size
    let _ ← arguments.toList.mapM (fun type =>
      if isNumeric type then .ok () else .error (.typeMismatch s!"argument of {name}"
        (atom "$int") type))
    let _ ← checkSame s!"arguments of {name}" arguments
    pure (atom "$o", signature)

private partial def checkTerm (signature : Signature)
    (variables : List (String × TypeExpr)) : Term →
    Except ValidationError (TypeExpr × Signature)
  | .variable name =>
      match variablesLookup variables name with
      | some type => .ok (type, signature)
      | none => .error (.unboundVariable name)
  | .constant symbol =>
      if isNumberOrDistinct symbol.raw then
        .ok (literalType symbol.raw, signature)
      else if definedTerms.contains symbol.raw || definedPredicates.contains symbol.raw ||
          symbol.raw == "$true" || symbol.raw == "$false" then
        .error (.invalidDefinedUse symbol.raw)
      else
        applyDeclared signature symbol #[] (atom "$i")
  | .function symbol arguments => do
      let (types, signature) ← checkTerms signature variables arguments.toList
      if isNumberOrDistinct symbol.raw then
        .error (.invalidApplication symbol.raw)
      else if definedPredicates.contains symbol.raw ||
          symbol.raw == "$true" || symbol.raw == "$false" then
        .error (.invalidDefinedUse symbol.raw)
      else if definedTerms.contains symbol.raw then
        definedTermType signature symbol types
      else
        applyDeclared signature symbol types (atom "$i")
end

private def checkAtom (signature : Signature)
    (variables : List (String × TypeExpr)) : Atom →
    Except ValidationError Signature
  | .predicate symbol arguments => do
      let (types, signature) ← checkTerms signature variables arguments.toList
      let (result, signature) ←
        if symbol.raw == "$true" || symbol.raw == "$false" then
          if arguments.isEmpty then .ok (atom "$o", signature)
          else .error (.invalidDefinedArity symbol.raw arguments.size)
        else if definedPredicates.contains symbol.raw then
          definedPredicateType signature symbol types
        else if definedTerms.contains symbol.raw then
          .error (.invalidDefinedUse symbol.raw)
        else
          applyDeclared signature symbol types (atom "$o")
      if result == atom "$o" then pure signature
      else throw (.typeMismatch s!"predicate {symbol.raw}" (atom "$o") result)
  | .equality left right | .inequality left right => do
      let (leftType, signature) ← checkTerm signature variables left
      let (rightType, signature) ← checkTerm signature variables right
      if isBoolean leftType || isKind leftType then
        throw (.invalidType "equality cannot compare $o or $tType")
      if leftType != rightType then
        throw (.typeMismatch "equality" leftType rightType)
      pure signature

private def firstDuplicate : List String → Option String
  | [] => none
  | name :: rest => if rest.contains name then some name else firstDuplicate rest

private def checkBinderTypes (signature : Signature)
    (variables : Array TypedVariable) : Except ValidationError (List (String × TypeExpr)) := do
  if variables.isEmpty then throw .emptyBinder
  match firstDuplicate (variables.toList.map TypedVariable.name) with
  | some name => throw (.duplicateBinder name)
  | none =>
      variables.toList.mapM fun binder => do
        let type := binder.type.getD (atom "$i")
        let _ ← typeKnown signature type
        pure (binder.name, type)

private partial def checkFormula (signature : Signature)
    (variables : List (String × TypeExpr)) : Formula →
    Except ValidationError Signature
  | .atom value => checkAtom signature variables value
  | .truth | .falsity => .ok signature
  | .not body => checkFormula signature variables body
  | .and left right
  | .or left right
  | .implies left right
  | .impliedBy left right
  | .iff left right
  | .xor left right
  | .nor left right
  | .nand left right => do
      let signature ← checkFormula signature variables left
      checkFormula signature variables right
  | .forall binders body | .exists binders body => do
      let bound ← checkBinderTypes signature binders
      checkFormula signature (bound ++ variables) body

/-- Validate a TF0 declaration and return the updated signature. -/
def validateDeclaration (signature : Signature) (declaration : Declaration) :
    Except ValidationError Signature := do
  let _ ← validateSignatureType signature declaration
  add signature declaration

/-- Validate one TF0 formula and return the signature including inferred defaults. -/
def validateFormula (signature : Signature) (formula : Formula) :
    Except ValidationError Signature :=
  checkFormula signature [] formula

/-- Validate one parsed TF0 body and return the updated signature. -/
def validateBody (signature : Signature) : Body → Except ValidationError Signature
  | .formula formula => validateFormula signature formula
  | .declaration declaration => validateDeclaration signature declaration

private def validateBodies : Signature → List Body → Except ValidationError Signature
  | signature, [] => .ok signature
  | signature, body :: rest => do
      let signature ← validateBody signature body
      validateBodies signature rest

/-- Validate a sequence of parsed TF0 bodies in source order. -/
def validateDocument (bodies : Array Body) : Except ValidationError Signature :=
  validateBodies {} bodies.toList

end TPTP.TFF
