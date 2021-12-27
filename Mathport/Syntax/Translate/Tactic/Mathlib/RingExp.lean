/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open Parser

-- # tactic.ring_exp
@[trTactic ring_exp_eq] def trRingExpEq : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring_exp_eq)
  | some _ => `(tactic| ring_exp_eq!)

@[trTactic ring_exp] def trRingExp : TacM Syntax := do
  let c ← parse (tk "!")?
  let loc ← trLoc (← parse location)
  match c with
  | none => `(tactic| ring_exp $(loc)?)
  | some _ => `(tactic| ring_exp! $(loc)?)

@[trConv ring_exp] def trRingExpConv : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(conv| ring_exp)
  | some _ => `(conv| ring_exp!)
