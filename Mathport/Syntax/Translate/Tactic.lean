/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Lean3
import Mathport.Syntax.Translate.Tactic.Mathlib

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport
namespace Translate
namespace Tactic

open AST3 Parser Lean.Elab.Command

open Lean.Elab.Command
def mkTacMap (l : Array (Name × TacM Syntax)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => tac.run a c s
  pure tacs

def mkNITacMap (l : Array (Name × (AST3.Expr → M Syntax))) :
  M (NameMap (AST3.Expr → CommandElabM Syntax)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => tac a c s
  pure tacs

def mkCmdMap (l : Array (Name × (Modifiers → TacM Unit))) :
  M (NameMap (Modifiers → Array (Spanned AST3.Param) → CommandElabM Unit)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun mod a => (tac mod).run a c s
  pure tacs

def builtinTactics := mkTacMap trTactics!
def builtinNITactics := mkNITacMap trNITactics!
def builtinConvs := mkTacMap trConvs!
def builtinUserNotation := mkTacMap trUserNotas!
def builtinUserAttrs := mkTacMap trUserAttrs!
def builtinUserCmds := mkCmdMap trUserCmds!
