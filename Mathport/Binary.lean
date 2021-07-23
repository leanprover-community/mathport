/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Binary.Basic
import Mathport.Binary.Path
import Mathport.Binary.Config
import Mathport.Binary.ParseTLean
import Mathport.Binary.Make

namespace Mathport.Binary

def main (args : List String) : IO Unit := do
  match args with
  | [lean4mod, mrp, pathToConfig] =>
    let config ← parseJsonFile Config pathToConfig
    let some lean3path ← config.modules[lean4mod] | throw (IO.userError s!"no such module '{lean4mod}'")
    make config lean4mod mrp
  | _ => throw $ IO.userError "usage: mathport binary <lean4mod> <lean3mrp> <recursive> <path-to-config>"

end Mathport.Binary
