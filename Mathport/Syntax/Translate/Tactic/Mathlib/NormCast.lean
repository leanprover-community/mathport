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

@[tr_user_attr norm_cast] def trNormCastAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun
  | some `elim => `(attr| norm_cast elim)
  | some `move => `(attr| norm_cast move)
  | some `squash => `(attr| norm_cast squash)
  | none => `(attr| norm_cast)
  | _ => warn! "unsupported (impossible)"

@[tr_tactic push_cast] def trPushCast : TacM Syntax.Tactic := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let loc ← trLoc (← parse location)
  `(tactic| push_cast $[[$hs,*]]? $[$loc:location]?)

@[tr_tactic norm_cast] def trNormCast : TacM Syntax.Tactic := do
  `(tactic| norm_cast $(← trLoc (← parse location))?)

@[tr_tactic rw_mod_cast] def trRwModCast : TacM Syntax.Tactic := do
  `(tactic| rw_mod_cast
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[tr_tactic exact_mod_cast] def trExactModCast : TacM Syntax.Tactic := do
  `(tactic| exact_mod_cast $(← trExpr (← parse pExpr)))

@[tr_tactic apply_mod_cast] def trApplyModCast : TacM Syntax.Tactic := do
  `(tactic| apply_mod_cast $(← trExpr (← parse pExpr)))

@[tr_tactic assumption_mod_cast] def trAssumptionModCast : TacM Syntax.Tactic := do
  `(tactic| assumption_mod_cast)

@[tr_conv norm_cast] def trNormCastConv : TacM Syntax.Conv := `(conv| norm_cast)
