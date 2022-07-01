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
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Tactic)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkConvMap (l : Array (Name × TacM Syntax)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Conv)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkTermMap (l : Array (Name × TacM Syntax)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Term)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkAttrMap (l : Array (Name × TacM Syntax)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Attr)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkNITacMap (l : Array (Name × (AST3.Expr → M Syntax))) :
  M (NameMap (AST3.Expr → CommandElabM Syntax.Tactic)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac a c s⟩
  pure tacs

def mkCmdMap (l : Array (Name × (Modifiers → TacM Unit))) :
  M (NameMap (Modifiers → Array (Spanned AST3.Param) → CommandElabM Unit)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun mod a => (tac mod).run n a c s
  pure tacs

def builtinTactics := mkTacMap trTactics!
def builtinNITactics := mkNITacMap trNITactics!
def builtinConvs := mkConvMap trConvs!
def builtinUserNotation := mkTermMap trUserNotas!
def builtinUserAttrs := mkAttrMap trUserAttrs!
def builtinUserCmds := mkCmdMap trUserCmds!
