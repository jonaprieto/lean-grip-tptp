/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.TFF
import TPTP.FirstOrder.Render

/-!
# TPTP.TFF.Render: canonical TF0 rendering
-/

namespace TPTP.TFF

private def join (values : Array String) : String :=
  String.intercalate ", " values.toList

private def joinProduct (values : Array String) : String :=
  String.intercalate " * " values.toList

partial def TypeExpr.render : TypeExpr → String
  | .atom symbol => symbol.render
  | .product elements => s!"({joinProduct (elements.map TypeExpr.render)})"
  | .mapping arguments result =>
      let domain := if arguments.size == 1 then
        arguments[0]?.map TypeExpr.render |>.getD ""
      else
        s!"({joinProduct (arguments.map TypeExpr.render)})"
      s!"{domain} > {result.render}"

instance : ToString TypeExpr where
  toString := TypeExpr.render

private def renderVariable (binder : TypedVariable) : String :=
  binder.type.map (fun type => s!"{binder.name}: {type.render}") |>.getD binder.name

partial def Formula.render : Formula → String
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

instance : ToString Formula where
  toString := Formula.render

def Declaration.render (declaration : Declaration) : String :=
  s!"{declaration.symbol.render}: {declaration.type.render}"

instance : ToString Declaration where
  toString := Declaration.render

end TPTP.TFF
