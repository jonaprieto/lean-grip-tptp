/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.FOF
import TPTP.FirstOrder.Render

/-!
# TPTP.FOF.Render: canonical first-order formula rendering

Binary formulas are always parenthesized because the FOF grammar does not assign general
precedence to its non-associative connectives.
-/

namespace TPTP.FOF

private def renderFormula : Formula → String
  | .atom value => value.render
  | .truth => "$true"
  | .falsity => "$false"
  | .not body => s!"~({renderFormula body})"
  | .and left right => s!"({renderFormula left} & {renderFormula right})"
  | .or left right => s!"({renderFormula left} | {renderFormula right})"
  | .implies left right => s!"({renderFormula left} => {renderFormula right})"
  | .impliedBy left right => s!"({renderFormula left} <= {renderFormula right})"
  | .iff left right => s!"({renderFormula left} <=> {renderFormula right})"
  | .xor left right => s!"({renderFormula left} <~> {renderFormula right})"
  | .nor left right => s!"({renderFormula left} ~| {renderFormula right})"
  | .nand left right => s!"({renderFormula left} ~& {renderFormula right})"
  | .forall variables body =>
      s!"! [{String.intercalate ", " variables.toList}] : ({renderFormula body})"
  | .exists variables body =>
      s!"? [{String.intercalate ", " variables.toList}] : ({renderFormula body})"

def Formula.render (formula : Formula) : String :=
  renderFormula formula

instance : ToString Formula where
  toString := Formula.render

end TPTP.FOF
