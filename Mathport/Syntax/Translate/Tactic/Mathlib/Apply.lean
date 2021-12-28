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

@[trTactic apply'] def trApply' : TacM Syntax := do
  `(tactic| apply' $(← trExpr (← parse pExpr)))

@[trTactic fapply'] def trFApply' : TacM Syntax := do
  `(tactic| fapply' $(← trExpr (← parse pExpr)))

@[trTactic eapply'] def trEApply' : TacM Syntax := do
  `(tactic| eapply' $(← trExpr (← parse pExpr)))

@[trTactic apply_with'] def trApplyWith' : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| apply_with' $[(config := $cfg)]? $e)

@[trTactic mapply'] def trMApply' : TacM Syntax := do
  `(tactic| mapply' $(← trExpr (← parse pExpr)))

@[trTactic reflexivity' refl'] def trRefl' : TacM Syntax := `(tactic| rfl')

@[trTactic symmetry'] def trSymmetry' : TacM Syntax := do
  `(tactic| symm' $(← trLoc (← parse location))?)

@[trTactic transitivity'] def trTransitivity' : TacM Syntax := do
  `(tactic| trans' $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)
