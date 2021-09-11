/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
open System (FilePath)

def createDirectoriesIfNotExists (path : FilePath) : IO Unit := do
  match System.FilePath.parent path with
  | some d => discard <| IO.Process.run { cmd := "mkdir", args := #["-p", d.toString] }
  | none   => pure ()
