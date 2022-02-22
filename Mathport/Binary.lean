/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Util.System
import Mathport.Bridge.Rename
import Mathport.Bridge.Config
import Mathport.Binary.Basic
import Mathport.Binary.Apply
import Mathport.Binary.ParseTLean

namespace Mathport

open Lean Lean.Elab.Command
open Binary

def binport1 (config : Config) (path : Path) : CommandElabM Unit := do
  let ϕ : BinportM Unit := do
    let mods ← parseTLean (path.toLean3 config.pathConfig ".tlean")
    for mod in mods do applyModification mod
    for mod in mods do applyModificationPost mod
    postprocessModule
  ϕ.run { config := config, path := path } |>.run' {}

end Mathport
