/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Binary.Basic
import Mathport.Binary.RenameExt
import Mathport.Binary.Config
import Mathport.Binary.ParseTLean
import Mathport.Binary.Make

namespace Mathport.Binary

def main (args : List String) : IO Unit := do
  match args with
  | [package, mod3, pathToConfig] =>
    let config ← parseJsonFile Config pathToConfig
    make config ⟨package, mod3.toName⟩
  | _ => throw $ IO.userError "usage: mathport binary <lean4mod> <lean3mrp> <path-to-config>"

end Mathport.Binary
