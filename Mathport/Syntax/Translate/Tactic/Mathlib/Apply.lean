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

@[tr_tactic apply'] def trApply' : TacM Syntax.Tactic := do
  `(tactic| apply $(← trExpr (← parse pExpr)))

attribute [tr_tactic fapply'] trFApply
attribute [tr_tactic eapply'] trEApply
attribute [tr_tactic apply_with'] trApplyWith
attribute [tr_tactic mapply'] trMApply
attribute [tr_tactic reflexivity' refl'] trRefl

@[tr_tactic symmetry'] def trSymmetry' : TacM Syntax.Tactic := do
  `(tactic| symm $(← trLoc (← parse location))?)

@[tr_tactic transitivity'] def trTransitivity' : TacM Syntax.Tactic := do
  `(tactic| trans $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)
