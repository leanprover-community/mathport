/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.Attributes
import Mathport.Syntax.Translate.Notation
import Mathport.Syntax.Translate.Parser
import Mathport.Syntax.Translate.Tactic

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open Lean.Elab (Visibility)

namespace Translate

open Std (HashMap)
open AST3

partial def M.run' (m : M α) :
  HashMap Name Name → Array Notation → Array Command → AuxData → CoreM α :=
  fun map nota cmds d => do
    let s ← ST.mkRef {notations := d}
    let rec ctx := ⟨map, nota, cmds, fun e => trExpr' e ctx s, fun c => trCommand' c ctx s⟩
    m ctx s

def M.run (m : M α) :
  HashMap Name Name → Array Notation → Array Command → StateT AuxData CoreM α :=
  M.run' $ do
    let mut tacs := {}
    for (n, tac) in Tactic.builtinTactics do
      tacs := tacs.insert n $ ← fun c s => pure fun a => tac.run a c s
    modify fun s => { s with tactics := tacs }
    (← m, (← get).notations)

end Translate

def AST3toData4 (renameMap : HashMap Name Name) (ast : AST3) : StateT Translate.AuxData CoreM Data4 :=
  (Translate.AST3toData4 ast).run renameMap ast.indexed_nota ast.indexed_cmds
