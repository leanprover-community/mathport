/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Bridge.Rename
import Mathport.Bridge.Config

namespace Mathport.Binary

open Lean Lean.Meta Lean.Elab.Command

structure Context where
  config   : Config
  path     : Path
  currDecl : Name := Name.anonymous

structure State where
  nNotations     : Nat                         := 0
  name2equations : HashMap Name (List Name)    := {}
  structures     : HashMap Name StructureDescr := {}

open Lean.Elab.Command in
abbrev BinportM := ReaderT Context $ StateRefT State CommandElabM

def sorryPlaceholderName : Name :=
  `_sorry_placeholder_

def mkSorryPlaceholder (type : Expr) : Expr :=
  mkApp (mkConst sorryPlaceholderName) type

def warnStr (msg : String) : BinportM Unit := do
  println! "[warning] while processing {(← read).path.mod3}::{(← read).currDecl}:\n{msg}"

def warn (ex : Exception) : BinportM Unit := do
  warnStr (← ex.toMessageData.toString)

def liftCoreM (x : CoreM α) : BinportM α := do
  Elab.Command.liftCoreM x

def liftMetaM (x : MetaM α) : BinportM α := do
  liftTermElabM (liftM x)

def addNameAlignment (n3 n4 : Name) (synthetic := false) (dubious := "") : BinportM Unit := do
  liftCoreM $ Mathlib.Prelude.Rename.addNameAlignment n3 n4 synthetic dubious

def addPossibleFieldName (n3 n4 : Name) : BinportM Unit := do
  liftCoreM $ Mathport.addPossibleFieldName n3 n4

def lookupNameExt (n3 : Name) : BinportM (Option Name) :=
  return Rename.resolveIdent? (← getEnv) n3 false |>.map (·.1.2)

def lookupNameExt! (n3 : Name) : BinportM Name := do
  match ← lookupNameExt n3 with
  | some n4 => pure n4
  | _       => throwError "[lookupNameExt!] name not found, {n3}"

def BinportM.toIO (x : BinportM α) (ctx : Context) (st : State) : Elab.Command.Context → Elab.Command.State → IO α :=
  ((x ctx).run' st).toIO

def BinportM.runIO (x : BinportM α) (ctx : Context) (env : Environment) : IO α := do
  let elabCtx := {
    fileName := ctx.path.toLean3 ctx.config.pathConfig "lean" |>.toString
    fileMap := dummyFileMap
    tacticCache? := none
  }
  toIO x ctx {} elabCtx (Lean.Elab.Command.mkState env)

end Mathport.Binary
