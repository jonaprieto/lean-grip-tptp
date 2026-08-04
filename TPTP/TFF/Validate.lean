/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.TFF.Render

/-!
# TPTP.TFF.Validate: TF0/TF1 signatures and type checking

Validation is intentionally an explicit pass. TFF permits default typing for
undeclared monomorphic symbols, while TF1 requires explicit type arguments for
polymorphic symbols. The validator handles both rules in source order.
-/

namespace TPTP.TFF

inductive ValidationError where
  | unboundVariable (name : String)
  | unboundTypeVariable (name : String)
  | emptyBinder
  | duplicateBinder (name : String)
  | invalidTypeScope
  | unknownType (name : String)
  | invalidType (message : String)
  | conflictingDeclaration (name : String) (previous : TypeExpr) (current : TypeExpr)
  | invalidArity (name : String) (expected actual : Nat)
  | invalidTypeArity (name : String) (expected actual : Nat)
  | invalidApplication (name : String)
  | invalidTypeArgument (name : String)
  | invalidDefinedUse (name : String)
  | invalidDefinedArity (name : String) (actual : Nat)
  | typeMismatch (context : String) (expected actual : TypeExpr)
  deriving BEq, Repr, Nonempty

instance : Inhabited TypeExpr := ⟨.atom { raw := "$i" }⟩

def ValidationError.message : ValidationError → String
  | .unboundVariable name => s!"unbound variable {name}"
  | .unboundTypeVariable name => s!"unbound type variable {name}"
  | .emptyBinder => "quantifier variable list cannot be empty"
  | .duplicateBinder name => s!"duplicate bound variable {name}"
  | .invalidTypeScope =>
      "a type-variable quantifier cannot occur below a term-variable quantifier"
  | .unknownType name => s!"unknown TFF type {name}"
  | .invalidType message => s!"invalid TFF type: {message}"
  | .conflictingDeclaration name previous current =>
      s!"conflicting declaration for {name}: {previous} versus {current}"
  | .invalidArity name expected actual =>
      s!"invalid arity {actual} for {name}; expected {expected}"
  | .invalidTypeArity name expected actual =>
      s!"invalid type-argument count {actual} for {name}; expected {expected}"
  | .invalidApplication name => s!"invalid application of {name}"
  | .invalidTypeArgument name => s!"invalid type argument for {name}"
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

private def canonicalTypeName : String → String
  | "$iType" => "$i"
  | "$oType" => "$o"
  | name => name

private def canonicalType : TypeExpr → TypeExpr
  | .atom symbol => .atom { symbol with raw := canonicalTypeName symbol.raw }
  | .application constructor arguments =>
      .application { constructor with raw := canonicalTypeName constructor.raw }
        (arguments.map canonicalType)
  | .product elements => .product (elements.map canonicalType)
  | .mapping arguments result =>
      .mapping (arguments.map canonicalType) (canonicalType result)
  | .forall variables body => .forall variables (canonicalType body)

private def canonicalSignature (signature : Signature) : Signature :=
  { declarations := signature.declarations.map fun declaration =>
      { declaration with type := canonicalType declaration.type } }

private def add (signature : Signature) (declaration : Declaration) :
    Except ValidationError Signature :=
  let declaration := { declaration with type := canonicalType declaration.type }
  match lookup signature declaration.symbol.raw with
  | none => .ok { declarations := signature.declarations.push declaration }
  | some previous =>
      if previous.type.alphaEquivalent declaration.type then
        .ok signature
      else
        .error (.conflictingDeclaration declaration.symbol.raw previous.type declaration.type)

private def atom (name : String) : TypeExpr :=
  .atom { raw := name }

private def isBuiltinType (name : String) : Bool :=
  ["$i", "$o", "$iType", "$oType", "$tType", "$int", "$rat", "$real"].contains name

private def isBoolean (type : TypeExpr) : Bool :=
  canonicalType type == atom "$o"

private def isKind (type : TypeExpr) : Bool :=
  canonicalType type == atom "$tType"

private def isNumeric (type : TypeExpr) : Bool :=
  ["$int", "$rat", "$real"].contains (match canonicalType type with
    | .atom symbol => symbol.raw
    | _ => "")

private def checkArity (name : String) (expected actual : Nat) :
    Except ValidationError Unit :=
  if expected == actual then .ok () else .error (.invalidArity name expected actual)

private def variablesLookup (variables : List (String × TypeExpr)) (name : String) :
    Option TypeExpr :=
  match variables with
  | [] => none
  | (bound, type) :: rest => if bound == name then some type else variablesLookup rest name

private def sameTypes (types : Array TypeExpr) : Option TypeExpr :=
  match types[0]? with
  | none => none
  | some first => if types.all (· == first) then some first else none

private def checkSame (context : String) (types : Array TypeExpr) :
    Except ValidationError TypeExpr :=
  let types := types.map canonicalType
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
  let expected := expected.map canonicalType
  let actual := actual.map canonicalType
  let _ ← checkArity name expected.size actual.size
  for pair in expected.zip actual do
    if pair.1 != pair.2 then
      throw (.typeMismatch s!"argument of {name}" pair.1 pair.2)

private def typeConstructorArity (declaration : Declaration) : Option Nat :=
  match declaration.type with
  | .mapping arguments result =>
      if isKind result && arguments.all isKind then some arguments.size else none
  | _ => none

private def typeVariableNames (variables : Array TypeBinder) : List String :=
  variables.toList.map TypeBinder.name

private def firstDuplicate : List String → Option String
  | [] => none
  | name :: rest => if rest.contains name then some name else firstDuplicate rest

private partial def typeKnown (signature : Signature) (typeVariables : List String)
    (type : TypeExpr) : Except ValidationError Unit :=
  match canonicalType type with
  | .atom symbol =>
      if typeVariables.contains symbol.raw then
        pure ()
      else if isBuiltinType symbol.raw then
        pure ()
      else
        match lookup signature symbol.raw with
        | some declaration =>
            match declaration.type with
            | .atom result =>
                if result.raw == "$tType" then pure ()
                else throw (.unknownType symbol.raw)
            | .mapping _ _ => throw (.invalidApplication symbol.raw)
            | .forall _ _ => throw (.invalidApplication symbol.raw)
            | .product _ => throw (.unknownType symbol.raw)
            | .application _ _ => throw (.unknownType symbol.raw)
        | none => throw (.unknownType symbol.raw)
  | .application constructor arguments =>
      match lookup signature constructor.raw with
      | some declaration =>
          match typeConstructorArity declaration with
          | some expected => do
              let _ ← checkArity constructor.raw expected arguments.size
              for argument in arguments do
                let _ ← typeKnown signature typeVariables argument
                if isBoolean argument || isKind argument then
                  throw (.invalidTypeArgument constructor.raw)
          | none => throw (.invalidApplication constructor.raw)
      | none => throw (.unknownType constructor.raw)
  | .product _ => throw (.invalidType "a product type must be part of a mapping")
  | .mapping _ _ => throw (.invalidType "a mapping type cannot be used as a term type")
  | .forall _ _ => throw (.invalidType "a polymorphic type cannot be used as a type argument")

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

private def validateTypeBinders (variables : Array TypeBinder) :
    Except ValidationError (List String) := do
  if variables.isEmpty then throw .emptyBinder
  let names := typeVariableNames variables
  match firstDuplicate names with
  | some name => throw (.duplicateBinder name)
  | none => pure names

private def validateMapping (signature : Signature) (typeVariables : List String)
    (arguments : Array TypeExpr) (result : TypeExpr) : Except ValidationError Unit := do
  if arguments.isEmpty then
    throw (.invalidType "a function, predicate, or type constructor needs an argument")
  if isKind result then
    for argument in arguments do
      if !isKind argument then
        throw (.invalidType "type-constructor arguments must have type $tType")
    pure ()
  else
    for argument in arguments do
      let _ ← typeKnown signature typeVariables argument
      if isBoolean argument || isKind argument then
        throw (.invalidType "TFF arguments cannot have type $o or $tType")
    let _ ← typeKnown signature typeVariables result
    pure ()

private def validateMonotype (signature : Signature) (typeVariables : List String) :
    TypeExpr → Except ValidationError Unit
  | type@(.atom _) => typeKnown signature typeVariables type
  | type@(.application _ _) => typeKnown signature typeVariables type
  | .mapping arguments result => validateMapping signature typeVariables arguments result
  | .product _ => .error (.invalidType "a product type must be part of a mapping")
  | .forall _ _ => .error (.invalidType "nested polymorphic type quantification is not TF1")

private def validateSignatureType (signature : Signature) (declaration : Declaration) :
    Except ValidationError Unit := do
  if !validDeclarationName declaration.symbol then
    throw (.invalidType s!"invalid declaration symbol {declaration.symbol.raw}")
  match declaration.type with
  | .forall variables body =>
      let names ← validateTypeBinders variables
      validateMonotype signature names body
  | type => validateMonotype signature [] type

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

private def defaultType (arity : Nat) (result : TypeExpr) : TypeExpr :=
  if arity == 0 then result else .mapping (Array.replicate arity (atom "$i")) result

private partial def termAsType (typeVariables : List String) :
    Term → Except ValidationError TypeExpr
  | .variable name =>
      if typeVariables.contains name then .ok (atom name)
      else .error (.unboundTypeVariable name)
  | .constant symbol => .ok (atom symbol.raw)
  | .function constructor arguments => do
      let arguments ← arguments.toList.mapM (termAsType typeVariables)
      pure (.application constructor arguments.toArray)

private def instantiate (variables : Array TypeBinder) (body : TypeExpr)
    (arguments : Array TypeExpr) : TypeExpr :=
  let substitution := (variables.toList.map TypeBinder.name).zip arguments.toList |>.toArray
  body.substitute substitution

private def applyMonotype (name : String) (type : TypeExpr) (arguments : Array TypeExpr) :
    Except ValidationError TypeExpr :=
  match type with
  | .mapping expected result => do
      let _ ← checkArguments name expected arguments
      pure result
  | .atom _ | .application _ _ =>
      if arguments.isEmpty then pure type else .error (.invalidArity name 0 arguments.size)
  | .product _ | .forall _ _ => .error (.invalidApplication name)

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

mutual
private partial def checkTerms (signature : Signature) (typeVariables : List String)
    (variables : List (String × TypeExpr)) :
    List Term → Except ValidationError (Array TypeExpr × Signature)
  | [] => .ok (#[], signature)
  | term :: rest => do
      let (type, signature) ← checkTerm signature typeVariables variables term
      let (types, signature) ← checkTerms signature typeVariables variables rest
      pure (#[type] ++ types, signature)

private partial def applyDeclared (signature : Signature) (typeVariables : List String)
    (variables : List (String × TypeExpr)) (symbol : Symbol) (arguments : Array Term)
    (defaultResult : TypeExpr) : Except ValidationError (TypeExpr × Signature) := do
  if symbol.raw.startsWith "$" && !symbol.raw.startsWith "$$" then
    throw (.invalidDefinedUse symbol.raw)
  match lookup signature symbol.raw with
  | none =>
      let (types, signature) ← checkTerms signature typeVariables variables arguments.toList
      let inferred := defaultType types.size defaultResult
      let result ← applyMonotype symbol.raw inferred types
      let declaration := { symbol, type := inferred }
      let signature ← add signature declaration
      pure (result, signature)
  | some declaration =>
      match declaration.type with
      | .forall binders body =>
          let expected := binders.size
          if arguments.size < expected then
            throw (.invalidTypeArity symbol.raw expected arguments.size)
          let typeTerms := arguments.toList.take expected |>.toArray
          let typeArguments ← typeTerms.toList.mapM (termAsType typeVariables)
          for typeArgument in typeArguments do
            let _ ← typeKnown signature typeVariables typeArgument
            if isBoolean typeArgument || isKind typeArgument then
              throw (.invalidTypeArgument symbol.raw)
          let instantiated := instantiate binders body typeArguments.toArray
          let termArguments := arguments.toList.drop expected
          let (types, signature) ←
            checkTerms signature typeVariables variables termArguments
          let result ← applyMonotype symbol.raw instantiated types
          pure (result, signature)
      | type =>
          let (types, signature) ← checkTerms signature typeVariables variables arguments.toList
          let result ← applyMonotype symbol.raw type types
          pure (result, signature)

private partial def checkTerm (signature : Signature) (typeVariables : List String)
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
        applyDeclared signature typeVariables variables symbol #[] (atom "$i")
  | .function symbol arguments => do
      if isNumberOrDistinct symbol.raw then
        throw (.invalidApplication symbol.raw)
      if definedPredicates.contains symbol.raw || symbol.raw == "$true" ||
          symbol.raw == "$false" then
        throw (.invalidDefinedUse symbol.raw)
      if definedTerms.contains symbol.raw then
        let (types, signature) ← checkTerms signature typeVariables variables arguments.toList
        definedTermType signature symbol types
      else
        applyDeclared signature typeVariables variables symbol arguments (atom "$i")
end

private def checkAtom (signature : Signature) (typeVariables : List String)
    (variables : List (String × TypeExpr)) : Atom →
    Except ValidationError Signature
  | .predicate symbol arguments => do
      let (result, signature) ←
        if symbol.raw == "$true" || symbol.raw == "$false" then
          if arguments.isEmpty then .ok (atom "$o", signature)
          else .error (.invalidDefinedArity symbol.raw arguments.size)
        else if definedPredicates.contains symbol.raw then
          let (types, signature) ← checkTerms signature typeVariables variables arguments.toList
          definedPredicateType signature symbol types
        else if definedTerms.contains symbol.raw then
          .error (.invalidDefinedUse symbol.raw)
        else
          applyDeclared signature typeVariables variables symbol arguments (atom "$o")
      if result == atom "$o" then pure signature
      else throw (.typeMismatch s!"predicate {symbol.raw}" (atom "$o") result)
  | .equality left right | .inequality left right => do
      let (leftType, signature) ← checkTerm signature typeVariables variables left
      let (rightType, signature) ← checkTerm signature typeVariables variables right
      if isBoolean leftType || isKind leftType then
        throw (.invalidType "equality cannot compare $o or $tType")
      if leftType != rightType then
        throw (.typeMismatch "equality" leftType rightType)
      pure signature

private def checkBinders (signature : Signature) (typeVariables : List String)
    (termVariables : List (String × TypeExpr)) (variables : Array TypedVariable) :
    Except ValidationError (List (String × TypeExpr) × List String) := do
  if variables.isEmpty then throw .emptyBinder
  let names := variables.toList.map TypedVariable.name
  match firstDuplicate names with
  | some name => throw (.duplicateBinder name)
  | none => pure ()
  let localTypeVariables := variables.toList.filterMap fun binder =>
    if binder.type.map canonicalType == some (atom "$tType") then some binder.name else none
  if !termVariables.isEmpty && !localTypeVariables.isEmpty then
    throw .invalidTypeScope
  let typeScope := localTypeVariables ++ typeVariables
  let mut terms : List (String × TypeExpr) := []
  let mut termSeen := false
  for binder in variables do
    let type := canonicalType (binder.type.getD (atom "$i"))
    if isKind type then
      if termSeen then throw .invalidTypeScope
      if typeVariables.contains binder.name || termVariables.any (·.1 == binder.name) then
        throw (.duplicateBinder binder.name)
    else
      let _ ← typeKnown signature typeScope type
      terms := terms.concat (binder.name, type)
      termSeen := true
  pure (terms, localTypeVariables)

private partial def checkFormula (signature : Signature) (typeVariables : List String)
    (variables : List (String × TypeExpr)) : Formula →
    Except ValidationError Signature
  | .atom value => checkAtom signature typeVariables variables value
  | .truth | .falsity => .ok signature
  | .not body => checkFormula signature typeVariables variables body
  | .and left right
  | .or left right
  | .implies left right
  | .impliedBy left right
  | .iff left right
  | .xor left right
  | .nor left right
  | .nand left right => do
      let signature ← checkFormula signature typeVariables variables left
      checkFormula signature typeVariables variables right
  | .forall binders body | .exists binders body | .unique binders body => do
      let (terms, types) ← checkBinders signature typeVariables variables binders
      checkFormula signature (types ++ typeVariables) (terms ++ variables) body

/-- Validate a TF0/TF1 declaration and return the updated signature. -/
def validateDeclaration (signature : Signature) (declaration : Declaration) :
    Except ValidationError Signature := do
  let signature := canonicalSignature signature
  let declaration := { declaration with type := canonicalType declaration.type }
  let _ ← validateSignatureType signature declaration
  add signature declaration

/-- Validate one typed formula and return the signature including inferred defaults. -/
def validateFormula (signature : Signature) (formula : Formula) :
    Except ValidationError Signature :=
  checkFormula (canonicalSignature signature) [] [] formula

/-- Validate one parsed typed body and return the updated signature. -/
def validateBody (signature : Signature) : Body → Except ValidationError Signature
  | .formula formula => validateFormula signature formula
  | .declaration declaration => validateDeclaration signature declaration

private def validateBodies : Signature → List Body → Except ValidationError Signature
  | signature, [] => .ok signature
  | signature, body :: rest => do
      let signature ← validateBody signature body
      validateBodies signature rest

/-- Validate a sequence of parsed typed bodies in source order. -/
def validateDocument (bodies : Array Body) : Except ValidationError Signature :=
  validateBodies {} bodies.toList

end TPTP.TFF
