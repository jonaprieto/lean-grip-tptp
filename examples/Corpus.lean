/-
Copyright (c) 2026 Jonathan Prieto-Cubides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Prieto-Cubides
-/

import TPTP

open TPTP

private def checkFile (path : String) : IO Unit := do
  let source ← IO.FS.readFile path
  match parseString source with
  | .ok _ => pure ()
  | .error error =>
      throw (IO.userError s!"{path}:\n{error.pretty source.toUTF8}")

def main (arguments : List String) : IO Unit := do
  let paths := match arguments with
    | "--" :: rest => rest
    | rest => rest
  if paths.isEmpty then
    throw (IO.userError "usage: lake exe corpus -- FILE...")
  for path in paths do
    checkFile path
  IO.println s!"TPTP corpus: {paths.length} files parsed"
