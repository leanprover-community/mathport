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

-- # tactic.norm_cast

@[trUserAttr norm_cast] def trNormCastAttr : TacM Syntax := do
  match ← parse (ident)? with
  | some `elim => `(attr| norm_cast elim)
  | some `move => `(attr| norm_cast move)
  | some `squash => `(attr| norm_cast squash)
  | none => `(attr| norm_cast)
  | _ => warn! "unsupported (impossible)"

@[trTactic push_cast] def trPushCast : TacM Syntax := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let loc ← trLoc (← parse location)
  `(tactic| push_cast $[[$hs,*]]? $[$loc:location]?)

@[trTactic norm_cast] def trNormCast : TacM Syntax := do
  `(tactic| norm_cast $(← trLoc (← parse location))?)

@[trTactic rw_mod_cast] def trRwModCast : TacM Syntax := do
  `(tactic| rw_mod_cast
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[trTactic exact_mod_cast] def trExactModCast : TacM Syntax := do
  `(tactic| exact_mod_cast $(← trExpr (← parse pExpr)))

@[trTactic apply_mod_cast] def trApplyModCast : TacM Syntax := do
  `(tactic| apply_mod_cast $(← trExpr (← parse pExpr)))

@[trTactic assumption_mod_cast] def trAssumptionModCast : TacM Syntax := do
  `(tactic| assumption_mod_cast)

@[trConv norm_cast] def trNormCastConv : TacM Syntax := `(conv| norm_cast)
