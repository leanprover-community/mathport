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

structure State where
  nNotations     : Nat                      := 0
  name2equations : HashMap Name (List Name) := {}

open Lean.Elab.Command in
abbrev BinportM := ReaderT Context $ StateRefT State CommandElabM

def warnStr (msg : String) : BinportM Unit := do
  println! "[warning] while processing {(← read).path34.mrpath}::{(← read).currDecl}:\n{msg}"

def warn (ex : Exception) : BinportM Unit := do
  warnStr (← ex.toMessageData.toString)

def liftCoreM (x : CoreM α) : BinportM α := do
  Elab.Command.liftCoreM x

def liftMetaM (x : MetaM α) : BinportM α := do
  liftTermElabM (declName? := some (← read).currDecl) (liftM x)

def BinportM.toIO (x : BinportM α) (ctx : Context) (st : State) (cmdCtx : Elab.Command.Context) (cmdState : Elab.Command.State) : IO α := do
  match ← ((x ctx).run' st) cmdCtx |>.run' cmdState |>.toIO' with
  | Except.error (Exception.error _ msg)   => do throw $ IO.userError (← msg.toString)
  | Except.error (Exception.internal id _) => throw $ IO.userError $ "internal exception #" ++ toString id.idx
  | Except.ok a => pure a

def BinportM.runIO (x : BinportM α) (ctx : Context) (env : Environment) : IO α := do
  toIO x ctx {} { fileName := ctx.path34.mrpath.toString, fileMap := dummyFileMap } (Lean.Elab.Command.mkState env)

end Mathport.Binary
