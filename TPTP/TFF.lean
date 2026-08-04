/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FirstOrder

/-!
# TPTP.TFF: typed first-order syntax

This module models the TF0 and TF1 typed first-order fragments of TFF. It keeps
type checking separate from parsing: the parser preserves the syntax tree, while
`TPTP.TFF.Validate` checks declarations, scopes, applications, and types.
-/

namespace TPTP.TFF

abbrev Symbol := FirstOrder.Symbol
abbrev Term := FirstOrder.Term
abbrev Atom := FirstOrder.Atom

structure TypeBinder where
  name : String
  deriving BEq, Repr

inductive TypeExpr where
  | atom (symbol : Symbol)
  | application (constructor : Symbol) (arguments : Array TypeExpr)
  | product (elements : Array TypeExpr)
  | mapping (arguments : Array TypeExpr) (result : TypeExpr)
  | forall (variables : Array TypeBinder) (body : TypeExpr)
  deriving BEq, Repr

structure TypedVariable where
  name : String
  type : Option TypeExpr := none
  deriving BEq, Repr

inductive Formula where
  | atom (value : Atom)
  | truth
  | falsity
  | not (body : Formula)
  | and (left right : Formula)
  | or (left right : Formula)
  | implies (left right : Formula)
  | impliedBy (left right : Formula)
  | iff (left right : Formula)
  | xor (left right : Formula)
  | nor (left right : Formula)
  | nand (left right : Formula)
  | forall (variables : Array TypedVariable) (body : Formula)
  | exists (variables : Array TypedVariable) (body : Formula)
  | unique (variables : Array TypedVariable) (body : Formula)
  deriving BEq, Repr

structure Declaration where
  symbol : Symbol
  type : TypeExpr
  deriving BEq, Repr

inductive Body where
  | formula (value : Formula)
  | declaration (value : Declaration)
  deriving BEq, Repr

namespace TypeExpr.Internal

def substitutionLookup (substitution : Array (String × TypeExpr))
    (name : String) : Option TypeExpr :=
  substitution.find? (fun pair => pair.1 == name) |>.map Prod.snd

def isTypeVariable (name : String) : Bool :=
  match name.toList with
  | first :: _ => first.isUpper
  | [] => false

def appendUnique (values : Array String) (value : String) : Array String :=
  if values.toList.contains value then values else values.push value

def freeVariablesAux : TypeExpr → Array String
  | .atom symbol => if isTypeVariable symbol.raw then #[symbol.raw] else #[]
  | .application _ arguments | .product arguments =>
      arguments.foldl (fun result type =>
        (freeVariablesAux type).foldl appendUnique result) #[]
  | .mapping arguments result =>
      let values := arguments.foldl (fun values type =>
        (freeVariablesAux type).foldl appendUnique values) #[]
      (freeVariablesAux result).foldl appendUnique values
  | .forall variables body =>
      (freeVariablesAux body).filter (fun name =>
        !variables.any (fun binder => binder.name == name))

def binderNamesAux : TypeExpr → Array String
  | .atom _ => #[]
  | .application _ arguments | .product arguments =>
      arguments.foldl (fun result type =>
        (binderNamesAux type).foldl appendUnique result) #[]
  | .mapping arguments result =>
      let values := arguments.foldl (fun values type =>
        (binderNamesAux type).foldl appendUnique values) #[]
      (binderNamesAux result).foldl appendUnique values
  | .forall variables body =>
      let values := variables.toList.map TypeBinder.name |>.toArray
      (binderNamesAux body).foldl appendUnique values

def renameBound (oldName newName : String) : TypeExpr → TypeExpr
  | .atom symbol =>
      if symbol.raw == oldName then .atom { raw := newName } else .atom symbol
  | .application constructor arguments =>
      .application constructor (arguments.map (renameBound oldName newName))
  | .product elements => .product (elements.map (renameBound oldName newName))
  | .mapping arguments result =>
      .mapping (arguments.map (renameBound oldName newName)) (renameBound oldName newName result)
  | .forall variables body =>
      if variables.any (fun binder => binder.name == oldName) then
        .forall variables body
      else
        .forall variables (renameBound oldName newName body)

def maxLength (used : Array String) : Nat :=
  used.foldl (fun result value => max result value.length) 0

def freshFallback (base : String) (used : Array String) : String :=
  base ++ "_" ++ String.ofList (List.replicate (maxLength used + 1) '_')

def freshCandidate (base : String) (index : Nat) : String :=
  if index == 0 then base else s!"{base}_{index}"

def freshNameLoop (base : String) (used : Array String) (index fuel : Nat) : String :=
  match fuel with
  | 0 => freshFallback base used
  | fuel + 1 =>
      let candidate := freshCandidate base index
      if used.toList.contains candidate then
        freshNameLoop base used (index + 1) fuel
      else
        candidate

def freshName (base : String) (used : Array String) : String :=
  freshNameLoop base used 0 (used.size + 1)

def depth : TypeExpr → Nat
  | .atom _ => 0
  | .application _ arguments | .product arguments =>
      1 + arguments.foldl (fun result type => max result (depth type)) 0
  | .mapping arguments result =>
      1 + max (arguments.foldl (fun value type => max value (depth type)) 0) (depth result)
  | .forall _ body => 1 + depth body

private theorem foldMax_ge : ∀ (types : List TypeExpr) (init : Nat),
    init ≤ types.foldl (fun value type => max value (depth type)) init
  | [], init => by simp
  | _ :: types, init => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (foldMax_ge types _)

private theorem list_depth_mem : ∀ (types : List TypeExpr) (init : Nat) (type : TypeExpr),
    type ∈ types → depth type ≤ types.foldl (fun value type => max value (depth type)) init
  | [], _, _, h => by simp at h
  | head :: tail, init, type, h => by
      simp only [List.mem_cons] at h
      simp only [List.foldl_cons]
      cases h with
      | inl h =>
          subst type
          exact Nat.le_trans (Nat.le_max_right _ _) (foldMax_ge tail _)
      | inr h =>
          exact Nat.le_trans (list_depth_mem tail (max init (depth head)) type h)
            (by exact Nat.le_refl _)

private theorem array_depth_mem (types : Array TypeExpr) (type : TypeExpr) (h : type ∈ types) :
    depth type ≤ types.foldl (fun value type => max value (depth type)) 0 := by
  rw [← Array.foldl_toList]
  apply list_depth_mem types.toList 0 type
  exact Array.mem_def.mp h

private theorem list_foldl_map_congr_mem {α β γ : Type} (f : α → β)
    (g : γ → β → γ) (g' : γ → α → γ) :
    ∀ (values : List α) (init : γ),
      (∀ value, value ∈ values → ∀ accumulator,
        g accumulator (f value) = g' accumulator value) →
      (values.map f).foldl g init = values.foldl g' init
  | [], init, _ => rfl
  | value :: values, init, h => by
      simp only [List.map_cons, List.foldl_cons]
      rw [h value (by simp) init]
      apply list_foldl_map_congr_mem f g g' values _
      intro other hOther accumulator
      exact h other (by simp [hOther]) accumulator

private theorem array_foldl_map_congr_mem {α β γ : Type} (values : Array α) (f : α → β)
    (g : γ → β → γ) (g' : γ → α → γ)
    (h : ∀ value, value ∈ values → ∀ accumulator,
      g accumulator (f value) = g' accumulator value) (init : γ) :
    (values.map f).foldl g init = values.foldl g' init := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  apply list_foldl_map_congr_mem f g g' values.toList init
  intro value hValue accumulator
  exact h value (Array.mem_def.mpr hValue) accumulator

private theorem depth_renameBound (oldName newName : String) (type : TypeExpr) :
    depth (renameBound oldName newName type) = depth type := by
  cases type with
  | atom symbol =>
      simp only [renameBound]
      split <;> simp only [depth]
  | application constructor arguments =>
      simp only [renameBound, depth]
      rw [array_foldl_map_congr_mem]
      intro type hType accumulator
      rw [depth_renameBound oldName newName type]
  | product elements =>
      simp only [renameBound, depth]
      rw [array_foldl_map_congr_mem]
      intro type hType accumulator
      rw [depth_renameBound oldName newName type]
  | mapping arguments result =>
      simp only [renameBound, depth]
      rw [array_foldl_map_congr_mem]
      · rw [depth_renameBound oldName newName result]
      · intro type hType accumulator
        rw [depth_renameBound oldName newName type]
  | «forall» variables body =>
      simp only [renameBound]
      split
      · simp [depth]
      · simp only [depth]
        rw [depth_renameBound oldName newName body]
termination_by depth type
decreasing_by
  all_goals simp_wf
  all_goals simp_all [depth]
  all_goals try omega
  all_goals
    first
    | exact Nat.lt_of_le_of_lt (array_depth_mem _ _ ‹_›) (by omega)
    | exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
    | simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.lt_succ_self _

def renameBinderStep (replacementFree used : Array String)
    (state : Array TypeBinder × TypeExpr) (binder : TypeBinder) :
    Array TypeBinder × TypeExpr :=
  let (variables, body) := state
  if replacementFree.toList.contains binder.name then
    let fresh := freshName binder.name used
    (variables.push { binder with name := fresh }, renameBound binder.name fresh body)
  else
    (variables.push binder, body)

  private theorem depth_binderFold (replacementFree used : Array String) :
    ∀ (variables : List TypeBinder) (initial : Array TypeBinder) (body : TypeExpr),
      depth ((variables.foldl (renameBinderStep replacementFree used) (initial, body)).2) =
        depth body
  | [], initial, body => rfl
  | binder :: variables, initial, body => by
      simp only [List.foldl_cons]
      simp only [renameBinderStep]
      split
      · rw [depth_binderFold replacementFree used variables
          (initial.push { binder with name := freshName binder.name used })
          (renameBound binder.name (freshName binder.name used) body)]
        rw [depth_renameBound]
      · exact depth_binderFold replacementFree used variables (initial.push binder) body

@[simp] private theorem depth_binderFold_array (replacementFree used : Array String)
    (variables : Array TypeBinder) (body : TypeExpr) :
    depth ((variables.foldl (renameBinderStep replacementFree used) (#[], body)).2) =
      depth body := by
  rw [← Array.foldl_toList]
  exact depth_binderFold replacementFree used variables.toList #[] body

def substitutionFreeVariables (substitution : Array (String × TypeExpr)) : Array String :=
  substitution.foldl (fun result pair =>
    (freeVariablesAux pair.2).foldl appendUnique result) #[]

def substituteAux (type : TypeExpr) (substitution : Array (String × TypeExpr)) : TypeExpr :=
  match type with
  | .atom symbol => substitutionLookup substitution symbol.raw |>.getD (.atom symbol)
  | .application constructor arguments =>
      .application constructor (arguments.map (fun type => substituteAux type substitution))
  | .product elements => .product (elements.map (fun type => substituteAux type substitution))
  | .mapping arguments result =>
      .mapping (arguments.map (fun type => substituteAux type substitution))
        (substituteAux result substitution)
  | .forall variables sourceBody =>
      let replacementFree := substitutionFreeVariables substitution
      let boundNames := variables.toList.map TypeBinder.name |>.toArray
      let substitutionNames := substitution.map Prod.fst
      let used := ((variables.toList.map TypeBinder.name).toArray ++
        binderNamesAux sourceBody ++ freeVariablesAux sourceBody ++ substitutionNames ++
          replacementFree)
      let filtered := substitution.filter (fun pair =>
        !boundNames.toList.contains pair.1)
      .forall
        (variables.foldl (renameBinderStep replacementFree used) (#[], sourceBody)).1
        (substituteAux
          (variables.foldl (renameBinderStep replacementFree used) (#[], sourceBody)).2
          filtered)
termination_by depth type
decreasing_by
  all_goals simp_wf
  all_goals simp_all [depth]
  all_goals try omega
  all_goals
    first
    | exact Nat.lt_of_le_of_lt (array_depth_mem _ _ ‹_›) (by omega)
    | exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
    | have hDepth := depth_binderFold_array
        (substitutionFreeVariables substitution)
        ((variables.toList.map TypeBinder.name).toArray ++
          binderNamesAux sourceBody ++ freeVariablesAux sourceBody ++
          substitution.map Prod.fst ++ substitutionFreeVariables substitution)
        variables sourceBody
      change depth ((variables.foldl (renameBinderStep replacementFree used)
        (#[], sourceBody)).2) < 1 + depth sourceBody
      rw [hDepth]
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.lt_succ_self (depth sourceBody)

end TypeExpr.Internal

/-- Collect free type variables in source order. -/
def TypeExpr.freeVariables (type : TypeExpr) : Array String :=
  Internal.freeVariablesAux type

/-- Capture-avoiding substitution for the type variables in a type expression. -/
def TypeExpr.substitute (substitution : Array (String × TypeExpr)) (type : TypeExpr) : TypeExpr :=
  Internal.substituteAux type substitution

/-- Rename a bound type variable without capturing a free variable. -/
def TypeExpr.alphaRename (oldName newName : String) : TypeExpr → TypeExpr := fun type =>
  if oldName == newName then
    type
  else
    match type with
    | .atom symbol => .atom symbol
    | .application constructor arguments =>
        .application constructor (arguments.map (TypeExpr.alphaRename oldName newName))
    | .product elements => .product (elements.map (TypeExpr.alphaRename oldName newName))
    | .mapping arguments result =>
        .mapping (arguments.map (TypeExpr.alphaRename oldName newName))
          (TypeExpr.alphaRename oldName newName result)
    | .forall variables body =>
        if variables.any (fun binder => binder.name == oldName) then
          let used := ((variables.toList.map TypeBinder.name).toArray ++
            Internal.binderNamesAux body ++ Internal.freeVariablesAux body)
          let fresh :=
            if used.toList.contains newName then Internal.freshName newName used else newName
          .forall (variables.map (fun binder =>
            if binder.name == oldName then { binder with name := fresh } else binder))
            (Internal.renameBound oldName fresh body)
        else
          .forall variables (TypeExpr.alphaRename oldName newName body)

namespace TypeExpr.Internal

inductive AlphaType where
  | atom (name : String)
  | bound (index : Nat)
  | application (constructor : String) (arguments : Array AlphaType)
  | product (elements : Array AlphaType)
  | mapping (arguments : Array AlphaType) (result : AlphaType)
  | forall (arity : Nat) (body : AlphaType)
  deriving BEq, Repr

def boundIndex (name : String) : List String → Option Nat
  | [] => none
  | bound :: rest =>
      if bound == name then some 0 else (boundIndex name rest).map (· + 1)

def alphaNormalize : List String → TypeExpr → AlphaType
  | bound, .atom symbol =>
      match boundIndex symbol.raw bound with
      | some index => .bound index
      | none => .atom symbol.raw
  | bound, .application constructor arguments =>
      .application constructor.raw (arguments.map (alphaNormalize bound))
  | bound, .product elements => .product (elements.map (alphaNormalize bound))
  | bound, .mapping arguments result =>
      .mapping (arguments.map (alphaNormalize bound)) (alphaNormalize bound result)
  | bound, .forall variables body =>
      let names := variables.toList.map TypeBinder.name
      .forall variables.size (alphaNormalize (names ++ bound) body)

end TypeExpr.Internal

def TypeExpr.alphaEquivalent (left right : TypeExpr) : Bool :=
  TypeExpr.Internal.alphaNormalize [] left == TypeExpr.Internal.alphaNormalize [] right

end TPTP.TFF
