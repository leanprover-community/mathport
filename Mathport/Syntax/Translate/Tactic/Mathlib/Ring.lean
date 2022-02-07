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
@[trTactic ring1] def trRing1 : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring1)
  | some _ => `(tactic| ring1!)

def trRingMode (n : Name) : M Syntax :=
  if [`SOP, `raw, `horner].contains n then
    pure $ mkNode ``Parser.Tactic.ringMode #[mkIdent n]
  else warn! "bad ring mode"

@[trTactic ring_nf] def trRingNF : TacM Syntax := do
  let c ← parse (tk "!")?
  let mode ← liftM $ (← parse (ident)?).mapM trRingMode
  let loc ← trLoc (← parse location)
  match c with
  | none => `(tactic| ring_nf $(mode)? $(loc)?)
  | some _ => `(tactic| ring_nf! $(mode)? $(loc)?)

@[trTactic ring] def trRing : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring)
  | some _ => `(tactic| ring!)

@[trConv ring_nf] def trRingNFConv : TacM Syntax := do
  let c ← parse (tk "!")?
  let mode ← liftM $ (← parse (ident)?).mapM trRingMode
  match c with
  | none => `(conv| ring_nf $(mode)?)
  | some _ => `(conv| ring_nf! $(mode)?)

@[trConv ring] def trRingConv : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(conv| ring)
  | some _ => `(conv| ring!)
