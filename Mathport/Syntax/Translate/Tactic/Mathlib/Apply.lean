/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.apply

@[tr_tactic apply'] def trApply' : TacM Syntax := do
  `(tactic| apply' $(← trExpr (← parse pExpr)))

@[tr_tactic fapply'] def trFApply' : TacM Syntax := do
  `(tactic| fapply' $(← trExpr (← parse pExpr)))

@[tr_tactic eapply'] def trEApply' : TacM Syntax := do
  `(tactic| eapply' $(← trExpr (← parse pExpr)))

@[tr_tactic apply_with'] def trApplyWith' : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| apply_with' $[(config := $cfg)]? $e)

@[tr_tactic mapply'] def trMApply' : TacM Syntax := do
  `(tactic| mapply' $(← trExpr (← parse pExpr)))

@[tr_tactic reflexivity' refl'] def trRefl' : TacM Syntax := `(tactic| rfl')

@[tr_tactic symmetry'] def trSymmetry' : TacM Syntax := do
  `(tactic| symm' $(← trLoc (← parse location))?)

@[tr_tactic transitivity'] def trTransitivity' : TacM Syntax := do
  `(tactic| trans' $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)
