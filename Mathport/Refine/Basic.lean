/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util
import Mathport.Data4
import Mathport.Translate

namespace Mathport

open Lean Lean.Elab.Command

namespace Refine

structure Context where

structure State where

abbrev RefineM := ReaderT Context (StateRefT State CommandElabM)

def refineSyntax : Data4 → RefineM Syntax :=
  sorry

def toIO (x : RefineM α) (env : Environment) : IO α := do
  let commandElabM : CommandElabM α := x {} |>.run' {}
  let cmdCtx : Lean.Elab.Command.Context := {
    fileName := "TODO",
    fileMap  := dummyFileMap
  }
  let cmdState : Lean.Elab.Command.State := Lean.Elab.Command.mkState env
  let x₂ : Except Exception α ← (commandElabM cmdCtx).run' cmdState |>.toIO'
  match x₂ with
  | Except.error (Exception.error _ msg)   => do let e ← msg.toString; throw $ IO.userError e
  | Except.error (Exception.internal id _) => throw $ IO.userError $ "internal exception #" ++ toString id.idx
  | Except.ok a => pure a

end Refine

def refineSyntax (data4 : Data4) (env : Environment) : IO Syntax := do
  Refine.toIO (Refine.refineSyntax data4) env

end Mathport
