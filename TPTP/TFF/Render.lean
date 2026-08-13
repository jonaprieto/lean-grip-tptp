/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.TFF
import TPTP.FirstOrder.Render

/-!
# TPTP.TFF.Render: canonical TF0/TF1 rendering
-/

namespace TPTP.TFF

private def join (values : Array String) : String :=
  String.intercalate ", " values.toList

private def joinProduct (values : Array String) : String :=
  String.intercalate " * " values.toList

private def renderTypeBinder (binder : TypeBinder) : String :=
  s!"{binder.name}: $tType"

-- partiality: TypeExpr stores recursive children in Arrays. A total renderer would need a
-- separate depth-indexed traversal; keep the direct public API until that representation is
-- changed or a measured stack renderer is justified.
partial def TypeExpr.render : TypeExpr → String
  | .atom symbol => symbol.render
  | .application constructor arguments =>
      s!"{constructor.render}({String.intercalate ", " (arguments.toList.map TypeExpr.render)})"
  | .product elements => s!"({joinProduct (elements.map TypeExpr.render)})"
  | .mapping arguments result =>
      let domain := if arguments.size == 1 then
        arguments[0]?.map TypeExpr.render |>.getD ""
      else
        s!"({joinProduct (arguments.map TypeExpr.render)})"
      s!"{domain} > {result.render}"
  | .forall variables body =>
      let body := match body with
        | .mapping _ _ => s!"({body.render})"
        | _ => body.render
      s!"!>[{String.intercalate ", " (variables.toList.map renderTypeBinder)}] : {body}"

instance : ToString TypeExpr where
  toString := TypeExpr.render

private def renderVariable (binder : TypedVariable) : String :=
  binder.type.map (fun type => s!"{binder.name}: {type.render}") |>.getD binder.name

private def formulaDepth : Formula → Nat
  | .atom _ | .truth | .falsity => 0
  | .not body => formulaDepth body + 1
  | .and left right
  | .or left right
  | .implies left right
  | .impliedBy left right
  | .iff left right
  | .xor left right
  | .nor left right
  | .nand left right => max (formulaDepth left) (formulaDepth right) + 1
  | .forall _ body | .exists _ body | .unique _ body => formulaDepth body + 1

def Formula.render : Formula → String
  | .atom value => value.render
  | .truth => "$true"
  | .falsity => "$false"
  | .not body => s!"~({body.render})"
  | .and left right => s!"({left.render} & {right.render})"
  | .or left right => s!"({left.render} | {right.render})"
  | .implies left right => s!"({left.render} => {right.render})"
  | .impliedBy left right => s!"({left.render} <= {right.render})"
  | .iff left right => s!"({left.render} <=> {right.render})"
  | .xor left right => s!"({left.render} <~> {right.render})"
  | .nor left right => s!"({left.render} ~| {right.render})"
  | .nand left right => s!"({left.render} ~& {right.render})"
  | .forall variables body =>
      s!"! [{join (variables.map renderVariable)}] : ({body.render})"
  | .exists variables body =>
      s!"? [{join (variables.map renderVariable)}] : ({body.render})"
  | .unique variables body =>
      s!"# [{join (variables.map renderVariable)}] : ({body.render})"
termination_by formula => formulaDepth formula
decreasing_by
  simp_wf
  all_goals simp_all [formulaDepth]
  all_goals omega

instance : ToString Formula where
  toString := Formula.render

def Declaration.render (declaration : Declaration) : String :=
  s!"{declaration.symbol.render}: {declaration.type.render}"

instance : ToString Declaration where
  toString := Declaration.render

end TPTP.TFF
