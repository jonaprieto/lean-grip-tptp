/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP.Syntax

namespace TPTP

def Statement.render (statement : Statement) : String :=
  let annotation := statement.annotations.map (fun value => s!", {value}") |>.getD ""
  s!"{statement.kind}({statement.name}, {statement.role}, {statement.formula}{annotation})."

def Include.render (value : Include) : String :=
  let selection := value.selection.map (fun item => s!", {item}") |>.getD ""
  s!"include({value.path}{selection})."

def Item.render : Item → String
  | .statement value => value.render
  | .include value => Include.render value

def Document.render (document : Document) : String :=
  String.intercalate "\n" (document.items.toList.map Item.render)

end TPTP
