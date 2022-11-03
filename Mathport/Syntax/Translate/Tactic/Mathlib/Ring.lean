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

-- # tactic.ring
@[tr_tactic ring1 ring_exp_eq] def trRing1 : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring1)
  | some _ => `(tactic| ring1!)

def trRingMode : Name → M (TSyntax ``Parser.Tactic.ringMode)
  | `SOP => `(Parser.Tactic.ringMode| SOP)
  | `horner => `(Parser.Tactic.ringMode| horner)
  | `raw => `(Parser.Tactic.ringMode| raw)
  | _ => warn! "bad ring mode" | `(Parser.Tactic.ringMode| horner)

@[tr_tactic ring_nf] def trRingNF : TacM Syntax := do
  let c ← parse (tk "!")?
  let mode ← liftM $ (← parse (ident)?).mapM trRingMode
  let loc ← trLoc (← parse location)
  let cfg ← liftM $ (← expr?).mapM trExpr
  match c with
  | none => `(tactic| ring_nf $[(config := $cfg)]? $(mode)? $(loc)?)
  | some _ => `(tactic| ring_nf! $[(config := $cfg)]? $(mode)? $(loc)?)

@[tr_tactic ring] def trRing : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring)
  | some _ => `(tactic| ring!)

@[tr_tactic ring_exp] def trRingExp : TacM Syntax := do
  match ← parse (tk "!")?, ← trLoc (← parse location) with
  | none, none => `(tactic| ring)
  | some _, none => `(tactic| ring!)
  | none, some loc => `(tactic| ring_nf $loc:location)
  | some _, some loc => `(tactic| ring_nf! $loc:location)

@[tr_conv ring_nf] def trRingNFConv : TacM Syntax := do
  let c ← parse (tk "!")?
  let mode ← liftM $ (← parse (ident)?).mapM trRingMode
  let cfg ← liftM $ (← expr?).mapM trExpr
  match c with
  | none => `(conv| ring_nf $[(config := $cfg)]? $(mode)?)
  | some _ => `(conv| ring_nf! $[(config := $cfg)]? $(mode)?)

@[tr_conv ring ring_exp] def trRingConv : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(conv| ring)
  | some _ => `(conv| ring!)
