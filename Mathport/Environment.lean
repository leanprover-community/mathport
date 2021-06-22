/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util

namespace Mathport
open Lean

private def getImportsFor (lean3Filename : FilePath) : IO (List Import) := do
  -- TODO: parse header, translate module names, and then import them
  pure [{ module := `Init : Import }]

unsafe def withEnvironmentFor {α : Type} (lean3filename : FilePath) (opts : Options) (trustLevel : UInt32 := 0) (x : Environment → IO α) : IO α := do
  let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
  Lean.initSearchPath LEAN_PATH
  let imports ← getImportsFor lean3filename
  Lean.withImportModules imports (opts := {}) (trustLevel := 0) x

end Mathport
