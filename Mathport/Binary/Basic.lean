/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Binary.Config
import Mathport.Binary.Path

namespace Mathport.Binary

open Std (HashMap HashSet)
open Lean Lean.Meta Lean.Elab.Command

structure Context where
  config   : Config
  path34   : Path34
  currDecl : Name := Name.anonymous

-- TODO: this is really ProcessM (now that Parser has been split off)
structure State where
  nNotations     : Nat                      := 0
  name2equations : HashMap Name (List Name) := {}

open Lean.Elab.Command in
abbrev BinportM := ReaderT Context $ StateRefT State CommandElabM

def isAligned (n : Name) : BinportM Bool := do
  (← read).config.customAligns.contains n

def trName (n : Name) : BinportM Name :=
  -- TODO: lookup in either env extension or json
  -- TODO: separate `trName` (dict lookup) vs `computeNewName` (complicated)
  pure n

def trExpr (e : Expr) (reduce : Bool := false) : BinportM Expr :=
  -- TODO: names, numbers, auto-params
  pure e

def warnStr (msg : String) : BinportM Unit := do
  println! "[warning] while processing {(← read).path34.mrpath}::{(← read).currDecl}:\n{msg}"

def warn (ex : Exception) : BinportM Unit := do
  warnStr (← ex.toMessageData.toString)

def liftMetaM {α} (x : MetaM α) : BinportM α := do
  liftTermElabM (declName? := some (← read).currDecl) (liftM x)

def BinportM.toIO (x : BinportM α) (ctx : Context) (env : Environment) : IO α := do
  let x₁ : CommandElabM α := (x ctx).run' {}

  let cmdCtx : Lean.Elab.Command.Context := {
    fileName := path2dot ctx.path34.mrpath,
    fileMap  := dummyFileMap
  }

  let cmdState : Lean.Elab.Command.State := Lean.Elab.Command.mkState env

  match ← (x₁ cmdCtx).run' cmdState |>.toIO' with
  | Except.error (Exception.error _ msg)   => do throw $ IO.userError (← msg.toString)
  | Except.error (Exception.internal id _) => throw $ IO.userError $ "internal exception #" ++ toString id.idx
  | Except.ok a => pure a

end Mathport.Binary
