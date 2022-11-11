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
def mkTacMap (l : Array (Name × TacM Syntax.Tactic)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Tactic)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkConvMap (l : Array (Name × TacM Syntax.Conv)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Conv)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkTermMap (l : Array (Name × TacM Syntax.Term)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Term)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run n a c s⟩
  pure tacs

def mkAttrMap (l : Array (Name × Parse1 Syntax.Attr)) :
  M (NameMap (Array (Spanned AST3.Param) → CommandElabM Syntax.Attr)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac.run.run n a c s⟩
  pure tacs

def mkNITacMap (l : Array (Name × (AST3.Expr → M Syntax.Tactic))) :
  M (NameMap (AST3.Expr → CommandElabM Syntax.Tactic)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun a => return ⟨← tac a c s⟩
  pure tacs

def mkCmdMap (l : Array (Name × (Modifiers → Parse1 Unit))) :
  M (NameMap (Modifiers → Array (Spanned AST3.Param) → CommandElabM Unit)) := do
  let mut tacs := {}
  for (n, tac) in l do
    tacs := tacs.insert n $ ← fun c s => pure fun mod a => (tac mod).run.run n a c s
  pure tacs

def builtinTactics := mkTacMap tr_tactics%
def builtinNITactics := mkNITacMap tr_ni_tactics%
def builtinConvs := mkConvMap tr_convs%
def builtinUserNotation := mkTermMap tr_user_notas%
def builtinUserAttrs := mkAttrMap tr_user_attrs%
def builtinUserCmds := mkCmdMap tr_user_cmds%
