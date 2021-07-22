/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import Mathport.Binary.Basic
import Mathport.Binary.Path
import Mathport.Binary.Config
import Mathport.Binary.ParseTLean

namespace Mathport.Binary

def main (args : List String) : IO Unit := do
  match args with
  | [lean4mod, mrp, recursive, pathToConfig] =>
    if ← parseBool recursive then
      throw $ IO.userError "[binport] recursive NYI"
    else
      let config ← parseJsonFile Config pathToConfig
      let some lean3path ← config.modules[lean4mod] | throw (IO.userError s!"no such module '{lean4mod}'")
      let tleanPath := lean3path.join ⟨mrp ++ ".tlean"⟩
      let envModifications ← parseTLean tleanPath
      pure ()
  | _ => throw $ IO.userError "usage: mathport binary <lean4mod> <lean3mrp> <recursive> <path-to-config>"

end Mathport.Binary
