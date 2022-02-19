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
import Mathport.Syntax.Transform
import Init.Data.Array.QSort

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open Lean.Elab (Visibility)
open Lean.Elab.Command (CommandElabM)

namespace Translate

open Std (HashMap)
open AST3

partial def M.run' (m : M α) (notations : Array Notation) (commands : Array Command)
  (pcfg : Path.Config) : CommandElabM α := do
  let s ← ST.mkRef {}
  let rec ctx := {
    pcfg, notations, commands
    transform := Transform.transform
    trExpr := fun e => trExpr' e ctx s
    trCommand := fun c => trCommand' c ctx s }
  m ctx s

def M.run (m : M α) (comments : Array Comment) :
    (notations : Array Notation) → (commands : Array Command) →
    (pcfg : Path.Config) → CommandElabM α :=
  M.run' $ do
    let tactics ← Tactic.builtinTactics
    let niTactics ← Tactic.builtinNITactics
    let convs ← Tactic.builtinConvs
    let userNotas ← Tactic.builtinUserNotation
    let userAttrs ← Tactic.builtinUserAttrs
    let userCmds ← Tactic.builtinUserCmds
    modify fun s => { s with
      tactics, niTactics, convs, userNotas, userAttrs, userCmds,
      remainingComments := comments.qsort (positionToStringPos ·.start < positionToStringPos ·.start) |>.toList }
    m

end Translate

def AST3toData4 (ast : AST3) : (pcfg : Path.Config) → CommandElabM Data4 :=
  (Translate.AST3toData4 ast).run ast.comments ast.indexed_nota ast.indexed_cmds

def tactic3toSyntax (containingFile : AST3) (tac3 : Spanned AST3.Tactic) : (pcfg : Path.Config) → CommandElabM Syntax :=
  (Translate.trTactic tac3).run #[] containingFile.indexed_nota containingFile.indexed_cmds
