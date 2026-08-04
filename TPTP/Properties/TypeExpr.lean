/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides.
-/

import TPTP

/-!
# TPTP.Properties.TypeExpr: TFF1 operation contracts

These theorems state the general invariants relied on by capture-avoiding
substitution and alpha-renaming.  The representation remains named; freshness
is proved at the operation boundary.
-/

namespace TPTP.Properties

open TPTP.TFF

private theorem list_max_ge : ∀ (values : List String) (init : Nat),
    init ≤ values.foldl (fun n value => max n value.length) init
  | [], init => by simp
  | _ :: values, init => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (list_max_ge values _)

private theorem list_maxLength_mem : ∀ (values : List String) (init : Nat) (value : String),
    value ∈ values → value.length ≤ values.foldl (fun n value => max n value.length) init
  | [], _, _, h => by simp at h
  | head :: tail, init, value, h => by
      simp only [List.mem_cons] at h
      simp only [List.foldl_cons]
      cases h with
      | inl h =>
          subst value
          exact Nat.le_trans (Nat.le_max_right _ _) (list_max_ge tail _)
      | inr h =>
          exact list_maxLength_mem tail (max init head.length) value h

private theorem maxLength_mem (used : Array String) (value : String) (h : value ∈ used) :
    value.length ≤ TypeExpr.Internal.maxLength used := by
  change value.length ≤ used.foldl (fun n value => max n value.length) 0
  rw [← Array.foldl_toList]
  exact list_maxLength_mem used.toList 0 value (Array.mem_def.mp h)

theorem freshFallback_not_mem (base : String) (used : Array String) :
    TypeExpr.Internal.freshFallback base used ∉ used := by
  intro h
  have hLength := maxLength_mem used (TypeExpr.Internal.freshFallback base used) h
  have hTooLong : TypeExpr.Internal.maxLength used <
      (TypeExpr.Internal.freshFallback base used).length := by
    simp [TypeExpr.Internal.freshFallback, TypeExpr.Internal.maxLength, String.length]
    omega
  omega

private theorem freshNameLoop_not_mem (base : String) (used : Array String) :
    ∀ (index fuel : Nat), TypeExpr.Internal.freshNameLoop base used index fuel ∉ used
  | _, 0 => by exact freshFallback_not_mem base used
  | index, fuel + 1 => by
      simp only [TypeExpr.Internal.freshNameLoop]
      split
      · exact freshNameLoop_not_mem base used (index + 1) fuel
      · intro h
        have hContains : used.toList.contains
            (TypeExpr.Internal.freshCandidate base index) = true :=
          List.contains_iff_mem.mpr (Array.mem_def.mp h)
        simp_all

theorem freshName_not_mem (base : String) (used : Array String) :
    TypeExpr.Internal.freshName base used ∉ used := by
  exact freshNameLoop_not_mem base used 0 (used.size + 1)

/-- The name selected for an alpha-renamed binder is outside the protected set. -/
theorem alphaFreshName_not_mem (newName : String) (used : Array String) :
    (if used.toList.contains newName then TypeExpr.Internal.freshName newName used else newName) ∉ used := by
  by_cases h : used.toList.contains newName = true
  · have hUsed : newName ∈ used :=
      Array.mem_def.mpr (List.contains_iff_mem.mp h)
    rw [h]
    exact freshName_not_mem newName used
  · intro hUsed
    by_cases hNew : newName ∈ used
    · exact h (List.contains_iff_mem.mpr (Array.mem_def.mp hNew))
    · simp [hNew] at hUsed

theorem substitute_atom_equation (substitution : Array (String × TypeExpr))
    (symbol : Symbol) :
    (TypeExpr.atom symbol).substitute substitution =
      ((substitution.find? (fun pair : String × TypeExpr => pair.1 == symbol.raw)).map Prod.snd).getD
        (.atom symbol) := by
  simp [TypeExpr.substitute, TPTP.TFF.TypeExpr.Internal.substituteAux,
    TPTP.TFF.TypeExpr.Internal.substitutionLookup]

theorem substitute_application_equation (substitution : Array (String × TypeExpr))
    (constructor : Symbol) (arguments : Array TypeExpr) :
    (TypeExpr.application constructor arguments).substitute substitution =
      .application constructor (arguments.map (fun type => type.substitute substitution)) := by
  simp [TypeExpr.substitute, TPTP.TFF.TypeExpr.Internal.substituteAux]

theorem substitute_product_equation (substitution : Array (String × TypeExpr))
    (elements : Array TypeExpr) :
    (TypeExpr.product elements).substitute substitution =
      .product (elements.map (fun type => type.substitute substitution)) := by
  simp [TypeExpr.substitute, TPTP.TFF.TypeExpr.Internal.substituteAux]

theorem substitute_mapping_equation (substitution : Array (String × TypeExpr))
    (arguments : Array TypeExpr) (result : TypeExpr) :
    (TypeExpr.mapping arguments result).substitute substitution =
      .mapping (arguments.map (fun type => type.substitute substitution))
        (result.substitute substitution) := by
  simp [TypeExpr.substitute, TPTP.TFF.TypeExpr.Internal.substituteAux]

theorem alphaRename_same (name : String) (type : TypeExpr) :
    type.alphaRename name name = type := by
  have h : (name == name) = true := by simp
  unfold TypeExpr.alphaRename
  rw [h]
  simp

theorem alphaRename_atom (oldName newName : String) (symbol : Symbol) :
    (TypeExpr.atom symbol).alphaRename oldName newName = .atom symbol := by
  by_cases h : oldName == newName <;> simp [TypeExpr.alphaRename, h]

theorem freeVariables_atom (symbol : Symbol) :
    (TypeExpr.atom symbol).freeVariables =
      if TypeExpr.Internal.isTypeVariable symbol.raw then #[symbol.raw] else #[] := by
  simp [TPTP.TFF.TypeExpr.freeVariables,
    TPTP.TFF.TypeExpr.Internal.freeVariablesAux]

private theorem array_map_eq {α β : Type} (values : Array α) (f g : α → β)
    (h : ∀ value, value ∈ values → f value = g value) :
    values.map f = values.map g := by
  apply Array.ext
  · simp
  · intro index hLeft hRight
    have hi : index < values.size := by simpa using hLeft
    rw [Array.getElem_map, Array.getElem_map]
    apply h values[index]
    exact Array.getElem_mem hi

private def renameContext (old fresh : String) : List String → List String
  | [] => []
  | name :: rest => (if name == old then fresh else name) :: renameContext old fresh rest

private theorem boundIndex_rename_old (old fresh : String) :
    ∀ (pre outer : List String), old ∈ pre → fresh ∉ pre →
      TypeExpr.Internal.boundIndex old (pre ++ outer) =
        TypeExpr.Internal.boundIndex fresh (renameContext old fresh pre ++ outer)
  | [], _, h, _ => by simp at h
  | head :: tail, outer, hOld, hFresh => by
      simp only [List.mem_cons] at hOld hFresh
      by_cases hHead : head = old
      · subst head
        simp [renameContext, TypeExpr.Internal.boundIndex]
      · have hHeadOld : (head == old) = false := by simp [hHead]
        have hHeadFresh : fresh ≠ head := by
          intro h
          exact hFresh (by simp [h])
        have hFreshHead : head ≠ fresh := Ne.symm hHeadFresh
        simp [renameContext, TypeExpr.Internal.boundIndex, hHeadOld, hFreshHead]
        rw [boundIndex_rename_old old fresh tail outer]
        · exact hOld.resolve_left (fun h => hHead h.symm)
        · exact fun h => hFresh (by simp [h])

private theorem boundIndex_rename_other (old fresh name : String) :
    ∀ (pre outer : List String), name ≠ old → name ≠ fresh →
      TypeExpr.Internal.boundIndex name (pre ++ outer) =
        TypeExpr.Internal.boundIndex name (renameContext old fresh pre ++ outer)
  | [], _, _, _ => rfl
  | head :: tail, outer, hOld, hFresh => by
      by_cases hHeadOld : head = old
      · have hOldName : old ≠ name := Ne.symm hOld
        have hFreshName : fresh ≠ name := Ne.symm hFresh
        simp [renameContext, TypeExpr.Internal.boundIndex, hHeadOld, hOldName,
          hFreshName, boundIndex_rename_other old fresh name tail outer hOld hFresh]
      · have hHeadOldBool : (head == old) = false := by simp [hHeadOld]
        by_cases hHeadName : head = name
        · simp [renameContext, TypeExpr.Internal.boundIndex, hHeadOldBool,
            hHeadName, hOld, hFresh]
        · have hNameHead : name ≠ head := Ne.symm hHeadName
          simp [renameContext, TypeExpr.Internal.boundIndex, hHeadOldBool,
            hHeadName, hNameHead,
            boundIndex_rename_other old fresh name tail outer hOld hFresh]

private theorem appendUnique_mem_left (values : Array String) (name value : String)
    (h : name ∈ values) : name ∈ TypeExpr.Internal.appendUnique values value := by
  by_cases hValue : value ∈ values
  · simp [TypeExpr.Internal.appendUnique, hValue, h]
  · simp [TypeExpr.Internal.appendUnique, hValue, h]

private theorem fold_appendUnique_mem_left :
    ∀ (values : List String) (initial : Array String) (name : String),
      name ∈ initial → name ∈ values.foldl TypeExpr.Internal.appendUnique initial
  | [], initial, name, h => by exact h
  | value :: values, initial, name, h => by
      simp only [List.foldl_cons]
      apply fold_appendUnique_mem_left values
      exact appendUnique_mem_left initial name value h

private theorem fold_appendUnique_mem_right :
    ∀ (values : List String) (initial : Array String) (name : String),
      name ∈ values → name ∈ values.foldl TypeExpr.Internal.appendUnique initial
  | [], _, _, h => by simp at h
  | value :: values, initial, name, h => by
      simp only [List.mem_cons] at h
      simp only [List.foldl_cons]
      cases h with
      | inl h =>
          apply fold_appendUnique_mem_left values
          by_cases hInitial : name ∈ initial
          · exact appendUnique_mem_left initial name value hInitial
          · subst name
            have hValueInitial : value ∉ initial := by simpa using hInitial
            simp [TypeExpr.Internal.appendUnique, hValueInitial]
      | inr h =>
          apply fold_appendUnique_mem_right values
          exact h

private theorem array_fold_appendUnique_mem_left (values initial : Array String)
    (name : String) (h : name ∈ initial) :
    name ∈ values.foldl TypeExpr.Internal.appendUnique initial := by
  rw [← Array.foldl_toList]
  exact fold_appendUnique_mem_left values.toList initial name h

private theorem array_fold_appendUnique_mem_right (values initial : Array String)
    (name : String) (h : name ∈ values) :
    name ∈ values.foldl TypeExpr.Internal.appendUnique initial := by
  rw [← Array.foldl_toList]
  exact fold_appendUnique_mem_right values.toList initial name (Array.mem_def.mp h)

private theorem nested_fold_mem_left {α : Type} :
    ∀ (values : List α) (f : α → Array String) (initial : Array String)
      (name : String),
      name ∈ initial →
        name ∈ values.foldl (fun result item =>
          (f item).foldl TypeExpr.Internal.appendUnique result) initial
  | [], _, initial, _, h => by exact h
  | head :: tail, f, initial, name, h => by
      simp only [List.foldl_cons]
      apply nested_fold_mem_left tail f
      rw [← Array.foldl_toList]
      apply fold_appendUnique_mem_left
      exact h

private theorem nested_fold_mem {α : Type} (values : List α)
    (f : α → Array String) (initial : Array String) (value : α) (name : String) :
    value ∈ values → name ∈ f value →
      name ∈ values.foldl (fun result item =>
        (f item).foldl TypeExpr.Internal.appendUnique result) initial := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail ih =>
      intro hValue hName
      simp only [List.mem_cons, List.foldl_cons] at hValue ⊢
      cases hValue with
      | inl hHead =>
          subst value
          apply nested_fold_mem_left tail f
            ((f head).foldl TypeExpr.Internal.appendUnique initial) name
          rw [← Array.foldl_toList]
          apply fold_appendUnique_mem_right (f head).toList
          exact Array.mem_def.mp hName
      | inr hTail =>
          apply ih (initial := (f head).foldl TypeExpr.Internal.appendUnique initial)
            hTail hName

private theorem nested_array_fold_mem {α : Type} (values : Array α)
    (f : α → Array String) (initial : Array String) (value : α) (name : String) :
    value ∈ values → name ∈ f value →
      name ∈ values.foldl (fun result item =>
        (f item).foldl TypeExpr.Internal.appendUnique result) initial := by
  rw [← Array.foldl_toList]
  intro hValue hName
  apply nested_fold_mem values.toList f initial value name
  · exact Array.mem_def.mp hValue
  · exact hName

private def noName (name : String) : TypeExpr → Prop
  | .atom symbol => symbol.raw ≠ name
  | .application _ arguments | .product arguments =>
      ∀ type ∈ arguments, noName name type
  | .mapping arguments result =>
      (∀ type ∈ arguments, noName name type) ∧ noName name result
  | .forall variables body =>
      (∀ binder ∈ variables, binder.name ≠ name) ∧ noName name body

private theorem fold_mem_of_array_mem (values : Array TypeExpr)
    (f : TypeExpr → Array String) (type : TypeExpr) (name : String)
    (hType : type ∈ values) (hName : name ∈ f type) :
    name ∈ values.foldl (fun result item =>
      (f item).foldl TypeExpr.Internal.appendUnique result) #[] := by
  exact nested_array_fold_mem values f #[] type name hType hName

private theorem noName_of_not_mem (name : String)
    (hTypeName : TypeExpr.Internal.isTypeVariable name = true) :
    ∀ type : TypeExpr,
      name ∉ TypeExpr.Internal.binderNamesAux type →
      name ∉ TypeExpr.Internal.freeVariablesAux type →
      noName name type
  | .atom symbol, hBinders, hFree => by
      simp only [noName]
      intro hName
      subst name
      by_cases hVariable : TypeExpr.Internal.isTypeVariable symbol.raw
      · exact hFree (by simp [TypeExpr.Internal.freeVariablesAux, hVariable])
      · simp [TypeExpr.Internal.isTypeVariable, hTypeName] at hVariable
        exact Bool.noConfusion (hVariable.symm.trans hTypeName)
  | .application constructor arguments, hBinders, hFree => by
      simp only [noName]
      simp only [TypeExpr.Internal.binderNamesAux, TypeExpr.Internal.freeVariablesAux]
        at hBinders hFree
      intro type hType
      apply noName_of_not_mem name hTypeName type
      · intro h
        apply hBinders
        simpa only [TypeExpr.Internal.binderNamesAux] using
          (fold_mem_of_array_mem arguments TypeExpr.Internal.binderNamesAux
            type name hType h)
      · intro h
        apply hFree
        simpa only [TypeExpr.Internal.freeVariablesAux] using
          (fold_mem_of_array_mem arguments TypeExpr.Internal.freeVariablesAux
            type name hType h)
  | .product elements, hBinders, hFree => by
      simp only [noName]
      simp only [TypeExpr.Internal.binderNamesAux, TypeExpr.Internal.freeVariablesAux]
        at hBinders hFree
      intro type hType
      apply noName_of_not_mem name hTypeName type
      · intro h
        apply hBinders
        simpa only [TypeExpr.Internal.binderNamesAux] using
          (fold_mem_of_array_mem elements TypeExpr.Internal.binderNamesAux
            type name hType h)
      · intro h
        apply hFree
        simpa only [TypeExpr.Internal.freeVariablesAux] using
          (fold_mem_of_array_mem elements TypeExpr.Internal.freeVariablesAux
            type name hType h)
  | .mapping arguments result, hBinders, hFree => by
      simp only [noName]
      simp only [TypeExpr.Internal.binderNamesAux, TypeExpr.Internal.freeVariablesAux]
        at hBinders hFree
      constructor
      · intro type hType
        apply noName_of_not_mem name hTypeName type
        · intro h
          apply hBinders
          let initial := arguments.foldl (fun result item =>
            (TypeExpr.Internal.binderNamesAux item).foldl
              TypeExpr.Internal.appendUnique result) #[]
          apply array_fold_appendUnique_mem_left
            (TypeExpr.Internal.binderNamesAux result) initial name
          exact nested_array_fold_mem arguments TypeExpr.Internal.binderNamesAux #[]
            type name hType h
        · intro h
          apply hFree
          let initial := arguments.foldl (fun result item =>
            (TypeExpr.Internal.freeVariablesAux item).foldl
              TypeExpr.Internal.appendUnique result) #[]
          apply array_fold_appendUnique_mem_left
            (TypeExpr.Internal.freeVariablesAux result) initial name
          exact nested_array_fold_mem arguments TypeExpr.Internal.freeVariablesAux #[]
            type name hType h
      · apply noName_of_not_mem name hTypeName result
        · intro h
          apply hBinders
          let initial := arguments.foldl (fun result item =>
            (TypeExpr.Internal.binderNamesAux item).foldl
              TypeExpr.Internal.appendUnique result) #[]
          exact array_fold_appendUnique_mem_right
            (TypeExpr.Internal.binderNamesAux result) initial name h
        · intro h
          apply hFree
          let initial := arguments.foldl (fun result item =>
            (TypeExpr.Internal.freeVariablesAux item).foldl
              TypeExpr.Internal.appendUnique result) #[]
          exact array_fold_appendUnique_mem_right
            (TypeExpr.Internal.freeVariablesAux result) initial name h
  | .forall variables body, hBinders, hFree => by
      simp only [noName]
      simp only [TypeExpr.Internal.binderNamesAux, TypeExpr.Internal.freeVariablesAux]
        at hBinders hFree
      constructor
      · intro binder hBinder
        intro hName
        apply hBinders
        let initial := variables.toList.map TypeBinder.name |>.toArray
        have hBinderList : binder ∈ variables.toList := Array.mem_def.mp hBinder
        have hNames : binder.name ∈ variables.toList.map TypeBinder.name :=
          List.mem_map.mpr ⟨binder, hBinderList, rfl⟩
        have hInitial : name ∈ initial := by
          subst name
          exact Array.mem_def.mpr (by simpa [initial] using hNames)
        exact array_fold_appendUnique_mem_left
          (TypeExpr.Internal.binderNamesAux body) initial name hInitial
      · apply noName_of_not_mem name hTypeName body
        · intro h
          apply hBinders
          let initial := variables.toList.map TypeBinder.name |>.toArray
          exact array_fold_appendUnique_mem_right
            (TypeExpr.Internal.binderNamesAux body) initial name h
        · intro h
          apply hFree
          have hFiltered : name ∈ Array.filter
              (fun name => !variables.any (fun binder => binder.name == name))
              (TypeExpr.Internal.freeVariablesAux body) := by
            apply Array.mem_filter.mpr
            constructor
            · exact h
            · have hAnyFalse : variables.any (fun binder => binder.name == name) = false := by
                apply Bool.eq_false_iff.mpr
                intro hBinder
                rw [Array.any_eq_true] at hBinder
                rcases hBinder with ⟨index, hIndex, hBinder⟩
                have hBinderMem : variables[index] ∈ variables := Array.getElem_mem hIndex
                have hBinderName : (variables[index]).name = name := by simpa using hBinder
                apply hBinders
                let initial := variables.toList.map TypeBinder.name |>.toArray
                have hNames : (variables[index]).name ∈ variables.toList.map TypeBinder.name :=
                  List.mem_map.mpr ⟨variables[index], Array.mem_def.mp hBinderMem, rfl⟩
                have hInitial : name ∈ initial := by
                  exact Array.mem_def.mpr (by simpa [initial, hBinderName] using hNames)
                exact array_fold_appendUnique_mem_left
                  (TypeExpr.Internal.binderNamesAux body) initial name
                  (by simpa [hBinderName] using hInitial)
              simp [hAnyFalse]
          exact hFiltered

private theorem boundIndex_tail_other (old fresh name : String) :
    ∀ (front tail outer : List String), name ≠ old → name ≠ fresh →
      TypeExpr.Internal.boundIndex name
          (front ++ tail ++ outer) =
        TypeExpr.Internal.boundIndex name
          (front ++ renameContext old fresh tail ++ outer)
  | [], tail, outer, hOld, hFresh =>
      boundIndex_rename_other old fresh name tail outer hOld hFresh
  | head :: front, tail, outer, hOld, hFresh => by
      by_cases hHead : head = name
      · simp [TypeExpr.Internal.boundIndex, hHead]
      · have ih := boundIndex_tail_other old fresh name front tail outer hOld hFresh
        simpa [TypeExpr.Internal.boundIndex, hHead, List.append_assoc] using
          congrArg (Option.map (fun index => index + 1)) ih

private theorem boundIndex_mem_some :
    ∀ (name : String) (values : List String), name ∈ values →
      ∃ index, TypeExpr.Internal.boundIndex name values = some index
  | _, [], h => by simp at h
  | name, head :: tail, h => by
      simp only [List.mem_cons] at h
      by_cases hHead : head = name
      · subst head
        simp [TypeExpr.Internal.boundIndex]
      · cases h with
        | inl h => exact False.elim (hHead h.symm)
        | inr hTail =>
            rcases boundIndex_mem_some name tail hTail with ⟨index, hIndex⟩
            refine ⟨index + 1, ?_⟩
            simp [TypeExpr.Internal.boundIndex, hHead, hIndex]

private theorem renameContext_append_of_absent (old fresh : String) :
    ∀ (front tail : List String), old ∉ front → fresh ∉ front →
      renameContext old fresh (front ++ tail) =
        front ++ renameContext old fresh tail
  | [], tail, _, _ => rfl
  | head :: front, tail, hOld, hFresh => by
      simp only [List.mem_cons] at hOld hFresh
      have hOldHead : old ≠ head := fun h => hOld (Or.inl h)
      have hOldTail : old ∉ front := fun h => hOld (Or.inr h)
      have hFreshHead : fresh ≠ head := fun h => hFresh (Or.inl h)
      have hFreshTail : fresh ∉ front := fun h => hFresh (Or.inr h)
      simp [renameContext, hOldHead, hFreshHead]
      constructor
      · exact fun h => hOldHead h.symm
      · exact renameContext_append_of_absent old fresh front tail hOldTail hFreshTail

private theorem array_any_binder_name (variables : Array TypeBinder)
    (binder : TypeBinder) (hBinder : binder ∈ variables) :
    variables.any (fun value => value.name == binder.name) = true := by
  rw [Array.any_eq_true]
  rcases Array.getElem_of_mem hBinder with ⟨index, hIndex, hEq⟩
  exact ⟨index, hIndex, by simpa [hEq]⟩

private theorem alphaRename_binder_names (old fresh : String)
    (variables : Array TypeBinder) :
    (variables.map (fun binder =>
      if binder.name == old then { binder with name := fresh } else binder)).toList.map
        TypeBinder.name =
      renameContext old fresh (variables.toList.map TypeBinder.name) := by
  rw [Array.toList_map]
  induction variables.toList with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.append_cons, renameContext]
      by_cases h : head.name = old
      · simp [h]
        simpa [Function.comp_def] using ih
      · simp [h]
        simpa [Function.comp_def] using ih

private theorem chosen_fresh_not_mem (base : String) (used : Array String) :
    (if used.toList.contains base then TypeExpr.Internal.freshName base used else base) ∉ used := by
  by_cases h : used.toList.contains base = true
  · simp only [h, ↓reduceIte]
    exact freshName_not_mem base used
  · have hBase : base ∉ used := by
      intro hBase
      apply h
      exact List.contains_iff_mem.mpr (Array.mem_def.mp hBase)
    simp [h, hBase]

private theorem isTypeVariable_append (base suffix : String)
    (hBase : TypeExpr.Internal.isTypeVariable base = true) :
    TypeExpr.Internal.isTypeVariable (base ++ suffix) = true := by
  unfold TypeExpr.Internal.isTypeVariable at hBase ⊢
  rw [String.toList_append]
  cases hBaseList : base.toList with
  | nil => simp [hBaseList] at hBase
  | cons first rest =>
      simp [hBaseList] at hBase ⊢
      exact hBase

private theorem freshCandidate_isTypeVariable (base : String) (index : Nat)
    (hBase : TypeExpr.Internal.isTypeVariable base = true) :
    TypeExpr.Internal.isTypeVariable (TypeExpr.Internal.freshCandidate base index) = true := by
  cases index with
  | zero => simpa [TypeExpr.Internal.freshCandidate] using hBase
  | succ index =>
      have hBaseString : toString base = base := rfl
      have hUnderscore : toString "_" = "_" := rfl
      have hCandidate : TypeExpr.Internal.freshCandidate base (index + 1) =
          base ++ ("_" ++ toString (index + 1)) := by
        simp [TypeExpr.Internal.freshCandidate, hBaseString, hUnderscore,
          String.append_assoc]
      rw [hCandidate]
      exact isTypeVariable_append base ("_" ++ toString (index + 1)) hBase

private theorem freshFallback_isTypeVariable (base : String) (used : Array String)
    (hBase : TypeExpr.Internal.isTypeVariable base = true) :
    TypeExpr.Internal.isTypeVariable (TypeExpr.Internal.freshFallback base used) = true := by
  simpa [TypeExpr.Internal.freshFallback, String.append_assoc] using
    isTypeVariable_append base
      ("_" ++ String.ofList (List.replicate (TypeExpr.Internal.maxLength used + 1) '_')) hBase

private theorem freshNameLoop_isTypeVariable (base : String) (used : Array String)
    (index fuel : Nat) (hBase : TypeExpr.Internal.isTypeVariable base = true) :
    TypeExpr.Internal.isTypeVariable
        (TypeExpr.Internal.freshNameLoop base used index fuel) = true := by
  induction fuel generalizing index with
  | zero => exact freshFallback_isTypeVariable base used hBase
  | succ fuel ih =>
      simp only [TypeExpr.Internal.freshNameLoop]
      split
      · exact ih (index + 1)
      · exact freshCandidate_isTypeVariable base index hBase

private theorem freshName_isTypeVariable (base : String) (used : Array String)
    (hBase : TypeExpr.Internal.isTypeVariable base = true) :
    TypeExpr.Internal.isTypeVariable (TypeExpr.Internal.freshName base used) = true := by
  exact freshNameLoop_isTypeVariable base used 0 (used.size + 1) hBase

private theorem boundIndex_tail_old (old fresh : String) :
    ∀ (front tail outer : List String), old ∈ front →
      TypeExpr.Internal.boundIndex old
          (front ++ tail ++ outer) =
        TypeExpr.Internal.boundIndex old
          (front ++ renameContext old fresh tail ++ outer)
  | [], _, _, hFront => by simp at hFront
  | head :: front, tail, outer, hFront => by
      simp only [List.mem_cons] at hFront
      by_cases hHead : head = old
      · simp [TypeExpr.Internal.boundIndex, hHead]
      · have ih := boundIndex_tail_old old fresh front tail outer
          (Or.resolve_left hFront (fun h => hHead h.symm))
        simpa [TypeExpr.Internal.boundIndex, hHead, List.append_assoc] using
          congrArg (Option.map (fun index => index + 1)) ih

private theorem alphaNormalize_context_tail (old fresh : String) :
    ∀ (front tail outer : List String) (type : TypeExpr),
      old ∈ front → noName fresh type →
      TypeExpr.Internal.alphaNormalize
          (front ++ renameContext old fresh tail ++ outer) type =
        TypeExpr.Internal.alphaNormalize (front ++ tail ++ outer) type
  | front, tail, outer, .atom symbol, hOld, hFresh => by
      simp only [TypeExpr.Internal.alphaNormalize]
      simp only [noName] at hFresh
      by_cases hSymbolOld : symbol.raw = old
      · have hIndex := boundIndex_tail_old old fresh front tail outer hOld
        have hIndex' : TypeExpr.Internal.boundIndex old
            (front ++ (renameContext old fresh tail ++ outer)) =
            TypeExpr.Internal.boundIndex old (front ++ (tail ++ outer)) := by
          simpa [List.append_assoc] using hIndex.symm
        have hIndex'' : TypeExpr.Internal.boundIndex old
            (front ++ renameContext old fresh tail ++ outer) =
            TypeExpr.Internal.boundIndex old (front ++ tail ++ outer) := by
          simpa [List.append_assoc] using hIndex'
        simp only [hSymbolOld]
        rw [hIndex'']
      · by_cases hSymbolFresh : symbol.raw = fresh
        · exfalso
          exact hFresh hSymbolFresh
        · have hIndex := boundIndex_tail_other old fresh symbol.raw front tail outer
            hSymbolOld hSymbolFresh
          have hIndex' : TypeExpr.Internal.boundIndex symbol.raw
              (front ++ (renameContext old fresh tail ++ outer)) =
              TypeExpr.Internal.boundIndex symbol.raw (front ++ (tail ++ outer)) := by
            simpa [List.append_assoc] using hIndex.symm
          have hIndex'' : TypeExpr.Internal.boundIndex symbol.raw
              (front ++ renameContext old fresh tail ++ outer) =
              TypeExpr.Internal.boundIndex symbol.raw (front ++ tail ++ outer) := by
            simpa [List.append_assoc] using hIndex'
          rw [hIndex'']
  | front, tail, outer, .application constructor arguments, hOld, hFresh => by
      simp only [TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      apply congrArg (TypeExpr.Internal.AlphaType.application constructor.raw)
      apply array_map_eq
      intro type hType
      apply alphaNormalize_context_tail old fresh front tail outer type hOld
        (hFresh type hType)
  | front, tail, outer, .product elements, hOld, hFresh => by
      simp only [TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      apply congrArg TypeExpr.Internal.AlphaType.product
      apply array_map_eq
      intro type hType
      apply alphaNormalize_context_tail old fresh front tail outer type hOld
        (hFresh type hType)
  | front, tail, outer, .mapping arguments result, hOld, hFresh => by
      simp only [TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      congr 1
      · apply array_map_eq
        intro type hType
        apply alphaNormalize_context_tail old fresh front tail outer type hOld
          (hFresh.1 type hType)
      · apply alphaNormalize_context_tail old fresh front tail outer result hOld hFresh.2
  | front, tail, outer, .forall variables body, hOld, hFresh => by
      simp only [TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      apply congrArg (fun value => TypeExpr.Internal.AlphaType.forall variables.size value)
      simpa [List.append_assoc] using
        alphaNormalize_context_tail old fresh
          (variables.toList.map TypeBinder.name ++ front) tail outer body
          (by simp [hOld]) hFresh.2

private theorem alphaNormalize_renameBound (old fresh : String) :
    ∀ (front outer : List String) (type : TypeExpr),
      old ∈ front → fresh ∉ front → noName fresh type →
      TypeExpr.Internal.alphaNormalize
          (renameContext old fresh front ++ outer)
          (TypeExpr.Internal.renameBound old fresh type) =
        TypeExpr.Internal.alphaNormalize (front ++ outer) type
  | front, outer, .atom symbol, hOld, hFreshFront, hFresh => by
      simp only [TypeExpr.Internal.renameBound, TypeExpr.Internal.alphaNormalize]
      simp only [noName] at hFresh
      by_cases hSymbolOld : symbol.raw = old
      · have hIndex := boundIndex_rename_old old fresh front outer hOld hFreshFront
        have hSome := boundIndex_mem_some old (front ++ outer) (by
          simp [hOld])
        rcases hSome with ⟨index, hSome⟩
        have hIndexFresh := hIndex
        rw [hSome] at hIndexFresh
        simp [hSymbolOld, TypeExpr.Internal.alphaNormalize, hSome]
        rw [← hIndexFresh]
      · by_cases hSymbolFresh : symbol.raw = fresh
        · exfalso
          exact hFresh hSymbolFresh
        · have hIndex := boundIndex_rename_other old fresh symbol.raw front outer
            hSymbolOld hSymbolFresh
          simp [hSymbolOld, hSymbolFresh, TypeExpr.Internal.alphaNormalize]
          rw [← hIndex]
  | front, outer, .application constructor arguments, hOld, hFreshFront, hFresh => by
      simp only [TypeExpr.Internal.renameBound, TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      simp only [Array.map_map]
      apply congrArg (TypeExpr.Internal.AlphaType.application constructor.raw)
      apply array_map_eq
      intro type hType
      apply alphaNormalize_renameBound old fresh front outer type hOld hFreshFront
        (hFresh type hType)
  | front, outer, .product elements, hOld, hFreshFront, hFresh => by
      simp only [TypeExpr.Internal.renameBound, TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      simp only [Array.map_map]
      apply congrArg TypeExpr.Internal.AlphaType.product
      apply array_map_eq
      intro type hType
      apply alphaNormalize_renameBound old fresh front outer type hOld hFreshFront
        (hFresh type hType)
  | front, outer, .mapping arguments result, hOld, hFreshFront, hFresh => by
      simp only [TypeExpr.Internal.renameBound, TypeExpr.Internal.alphaNormalize, noName]
      simp only [noName] at hFresh
      simp only [Array.map_map]
      congr 1
      · apply array_map_eq
        intro type hType
        apply alphaNormalize_renameBound old fresh front outer type hOld hFreshFront
          (hFresh.1 type hType)
      · apply alphaNormalize_renameBound old fresh front outer result hOld hFreshFront hFresh.2
  | front, outer, .forall variables body, hOld, hFreshFront, hFresh => by
      simp only [noName] at hFresh
      by_cases hBinder : variables.any (fun binder => binder.name == old) = true
      · simp [TypeExpr.Internal.renameBound, hBinder, TypeExpr.Internal.alphaNormalize]
        have hOldNames : old ∈ variables.toList.map TypeBinder.name := by
          rw [Array.any_eq_true] at hBinder
          rcases hBinder with ⟨index, hIndex, hBinder⟩
          have hName : (variables[index]).name = old := by simpa using hBinder
          have hMem : variables[index] ∈ variables := Array.getElem_mem hIndex
          exact List.mem_map.mpr ⟨variables[index], Array.mem_def.mp hMem, hName⟩
        simpa [List.append_assoc] using
          alphaNormalize_context_tail old fresh
            (variables.toList.map TypeBinder.name)
            front outer body (by simpa using hOldNames) hFresh.2
      · have hRename : TypeExpr.Internal.renameBound old fresh
            (.forall variables body) =
            .forall variables (TypeExpr.Internal.renameBound old fresh body) := by
          simp [TypeExpr.Internal.renameBound, hBinder]
        rw [hRename]
        simp only [TypeExpr.Internal.alphaNormalize]
        apply congrArg (fun value => TypeExpr.Internal.AlphaType.forall variables.size value)
        have hOldNames : old ∈ variables.toList.map TypeBinder.name → False := by
          intro h
          apply hBinder
          rcases List.mem_map.mp h with ⟨binder, hMem, hName⟩
          have hAny := array_any_binder_name variables binder (Array.mem_def.mpr hMem)
          simpa [hName] using hAny
        have hFreshNames : fresh ∉ variables.toList.map TypeBinder.name := by
          intro h
          rcases List.mem_map.mp h with ⟨binder, hMem, hName⟩
          have hNo := hFresh.1 binder (Array.mem_def.mpr hMem)
          exact hNo (by simpa [hName])
        have hOldFront : old ∈ variables.toList.map TypeBinder.name ++ front := by
          simp [hOld, hOldNames]
        have hFreshFront' : fresh ∉ variables.toList.map TypeBinder.name ++ front := by
          simp [hFreshNames, hFreshFront]
        have ih := alphaNormalize_renameBound old fresh
          (variables.toList.map TypeBinder.name ++ front) outer body
          hOldFront hFreshFront' hFresh.2
        have hContext := renameContext_append_of_absent old fresh
          (variables.toList.map TypeBinder.name) front hOldNames hFreshNames
        rw [hContext] at ih
        simpa [List.append_assoc] using ih

private theorem alphaNormalize_alphaRename (old new : String)
    (hNew : TypeExpr.Internal.isTypeVariable new = true) :
    ∀ (bound : List String) (type : TypeExpr),
      TypeExpr.Internal.alphaNormalize bound (type.alphaRename old new) =
        TypeExpr.Internal.alphaNormalize bound type := by
  let P : TypeExpr → Prop := fun type =>
    ∀ bound : List String,
      TypeExpr.Internal.alphaNormalize bound (type.alphaRename old new) =
        TypeExpr.Internal.alphaNormalize bound type
  let PA : Array TypeExpr → Prop := fun values =>
    ∀ type, type ∈ values → P type
  let PL : List TypeExpr → Prop := fun values =>
    ∀ type, type ∈ values → P type
  have hall : ∀ type : TypeExpr, P type := by
    intro type
    refine @TypeExpr.rec P PA PL ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ type
    · intro symbol bound
      by_cases hSame : (old == new) = true
      · simp [P, TypeExpr.alphaRename, hSame]
      · simp [P, TypeExpr.alphaRename, hSame]
    · intro constructor arguments ihArguments bound
      by_cases hSame : (old == new) = true
      · simp [P, TypeExpr.alphaRename, hSame]
      · have hRename : TypeExpr.alphaRename old new
            (.application constructor arguments) =
            .application constructor (arguments.map (TypeExpr.alphaRename old new)) := by
          simp [TypeExpr.alphaRename, hSame]
        rw [hRename]
        simp only [P, TypeExpr.Internal.alphaNormalize]
        apply congrArg (TypeExpr.Internal.AlphaType.application constructor.raw)
        rw [Array.map_map]
        apply array_map_eq
        intro type hType
        exact ihArguments type hType bound
    · intro elements ihElements bound
      by_cases hSame : (old == new) = true
      · simp [P, TypeExpr.alphaRename, hSame]
      · have hRename : TypeExpr.alphaRename old new
            (.product elements) =
            .product (elements.map (TypeExpr.alphaRename old new)) := by
          simp [TypeExpr.alphaRename, hSame]
        rw [hRename]
        simp only [P, TypeExpr.Internal.alphaNormalize]
        apply congrArg TypeExpr.Internal.AlphaType.product
        rw [Array.map_map]
        apply array_map_eq
        intro type hType
        exact ihElements type hType bound
    · intro arguments result ihArguments ihResult bound
      by_cases hSame : (old == new) = true
      · simp [P, TypeExpr.alphaRename, hSame]
      · have hRename : TypeExpr.alphaRename old new
            (.mapping arguments result) =
            .mapping (arguments.map (TypeExpr.alphaRename old new))
              (TypeExpr.alphaRename old new result) := by
          simp [TypeExpr.alphaRename, hSame]
        rw [hRename]
        simp only [P, TypeExpr.Internal.alphaNormalize]
        congr 1
        · rw [Array.map_map]
          apply array_map_eq
          intro type hType
          exact ihArguments type hType bound
        · exact ihResult bound
    · intro variables body ihBody bound
      by_cases hSame : (old == new) = true
      · simp [P, TypeExpr.alphaRename, hSame]
      · by_cases hBinder : variables.any (fun binder => binder.name == old) = true
        · let used := (variables.toList.map TypeBinder.name).toArray ++
            TypeExpr.Internal.binderNamesAux body ++
            TypeExpr.Internal.freeVariablesAux body
          let fresh := if used.toList.contains new then
              TypeExpr.Internal.freshName new used else new
          have hFreshUsed : fresh ∉ used := chosen_fresh_not_mem new used
          have hFreshVariables : fresh ∉ variables.toList.map TypeBinder.name := by
            intro h
            apply hFreshUsed
            simp [used, h]
          have hFreshBinders : fresh ∉ TypeExpr.Internal.binderNamesAux body := by
            intro h
            apply hFreshUsed
            simp [used, h]
          have hFreshFree : fresh ∉ TypeExpr.Internal.freeVariablesAux body := by
            intro h
            apply hFreshUsed
            simp [used, h]
          have hFreshTypeVar : TypeExpr.Internal.isTypeVariable fresh = true := by
            dsimp [fresh]
            split
            · exact freshName_isTypeVariable new used hNew
            · exact hNew
          have hFreshType := noName_of_not_mem fresh hFreshTypeVar body
            hFreshBinders hFreshFree
          have hOldVariables : old ∈ variables.toList.map TypeBinder.name := by
            rw [Array.any_eq_true] at hBinder
            rcases hBinder with ⟨index, hIndex, hBinder⟩
            have hName : (variables[index]).name = old := by simpa using hBinder
            have hMem : variables[index] ∈ variables := Array.getElem_mem hIndex
            exact List.mem_map.mpr ⟨variables[index], Array.mem_def.mp hMem, hName⟩
          have hRenamed := alphaNormalize_renameBound old fresh
            (variables.toList.map TypeBinder.name) bound body
            hOldVariables hFreshVariables hFreshType
          have hNames := alphaRename_binder_names old fresh variables
          have hRename : TypeExpr.alphaRename old new (.forall variables body) =
              .forall
                (variables.map (fun binder =>
                  if binder.name == old then { binder with name := fresh } else binder))
                (TypeExpr.Internal.renameBound old fresh body) := by
            simp [TypeExpr.alphaRename, hSame, hBinder, used, fresh]
          rw [hRename]
          simp only [P, TypeExpr.Internal.alphaNormalize]
          simp only [Array.size_map]
          apply congrArg (fun value => TypeExpr.Internal.AlphaType.forall variables.size value)
          rw [hNames]
          exact hRenamed
        · have hRename : TypeExpr.alphaRename old new (.forall variables body) =
              .forall variables (TypeExpr.alphaRename old new body) := by
            simp [TypeExpr.alphaRename, hSame, hBinder]
          rw [hRename]
          simp only [P, TypeExpr.Internal.alphaNormalize]
          apply congrArg (fun value => TypeExpr.Internal.AlphaType.forall variables.size value)
          exact ihBody (variables.toList.map TypeBinder.name ++ bound)
    · intro values ihValues type hType
      exact ihValues type (Array.mem_def.mp hType)
    · intro type hType
      simp at hType
    · intro head tail ihHead ihTail type hType
      simp only [List.mem_cons] at hType
      cases hType with
      | inl hHead =>
          subst type
          exact ihHead
      | inr hTail => exact ihTail type hTail
  intro bound type
  exact hall type bound

def typeAlphaEquivalent (left right : TypeExpr) : Prop :=
  TypeExpr.Internal.alphaNormalize [] left = TypeExpr.Internal.alphaNormalize [] right

theorem alphaRename_alphaEquivalent (old new : String) (type : TypeExpr)
    (hNew : TypeExpr.Internal.isTypeVariable new = true) :
    typeAlphaEquivalent (type.alphaRename old new) type :=
  alphaNormalize_alphaRename old new hNew [] type

theorem alphaRename_freshness (old new : String) (variables : Array TypeBinder)
    (body : TypeExpr) :
    let used := (variables.toList.map TypeBinder.name).toArray ++
      TypeExpr.Internal.binderNamesAux body ++ TypeExpr.Internal.freeVariablesAux body
    let fresh := if used.toList.contains new then
        TypeExpr.Internal.freshName new used else new
    fresh ∉ used := by
  dsimp
  exact alphaFreshName_not_mem new _

theorem substitute_freshness (substitution : Array (String × TypeExpr))
    (variables : Array TypeBinder) (body : TypeExpr) (binder : TypeBinder) :
    let replacementFree := TypeExpr.Internal.substitutionFreeVariables substitution
    let used := (variables.toList.map TypeBinder.name).toArray ++
      TypeExpr.Internal.binderNamesAux body ++ TypeExpr.Internal.freeVariablesAux body ++
      substitution.map Prod.fst ++ replacementFree
    TypeExpr.Internal.freshName binder.name used ∉ used := by
  dsimp
  exact freshName_not_mem binder.name _

theorem substitute_forall_equation (substitution : Array (String × TypeExpr))
    (variables : Array TypeBinder) (body : TypeExpr) :
    (TypeExpr.forall variables body).substitute substitution =
      let replacementFree := TypeExpr.Internal.substitutionFreeVariables substitution
      let boundNames := (variables.toList.map TypeBinder.name).toArray
      let substitutionNames := substitution.map Prod.fst
      let used := boundNames ++ TypeExpr.Internal.binderNamesAux body ++
        TypeExpr.Internal.freeVariablesAux body ++ substitutionNames ++ replacementFree
      let filtered := substitution.filter (fun pair =>
        !boundNames.toList.contains pair.1)
      let renamed := variables.foldl
        (TypeExpr.Internal.renameBinderStep replacementFree used) (#[], body)
      TypeExpr.forall renamed.1 (TypeExpr.Internal.substituteAux renamed.2 filtered) := by
  simp [TypeExpr.substitute, TypeExpr.Internal.substituteAux]

#print axioms freshFallback_not_mem
#print axioms freshName_not_mem
#print axioms alphaFreshName_not_mem
#print axioms substitute_atom_equation
#print axioms substitute_application_equation
#print axioms substitute_product_equation
#print axioms substitute_mapping_equation
#print axioms alphaRename_same
#print axioms alphaRename_atom
#print axioms freeVariables_atom
#print axioms alphaRename_alphaEquivalent
#print axioms alphaRename_freshness
#print axioms substitute_freshness
#print axioms substitute_forall_equation

end TPTP.Properties
