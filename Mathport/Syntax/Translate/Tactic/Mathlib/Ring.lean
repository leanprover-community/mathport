/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open Parser Mathlib.Tactic

-- # tactic.ring
@[tr_tactic ring1 ring_exp_eq] def trRing1 : TacM Syntax.Tactic := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring1)
  | some _ => `(tactic| ring1!)

def parseRingNFConfig : Option (Spanned AST3.Expr) → M RingNF.Config
  | none
  | some ⟨_, AST3.Expr.«{}»⟩ => pure {}
  | some ⟨_, AST3.Expr.structInst _ none flds #[] false⟩ => do
    let mut cfg : RingNF.Config := {}
    for (⟨_, n⟩, e) in flds do
      match n, e.kind with
      | `recursive, e => cfg := parseSimpConfig.asBool e cfg fun cfg b => {cfg with recursive := b}
      | _, _ => warn! "warning: unsupported ring_nf config option: {n}"
    pure cfg
  | some _ => warn! "warning: unsupported ring_nf config syntax" | pure {}

instance : Quote RingNF.RingMode where
  quote x := Id.run `(.$(mkIdent <| match x with | .SOP => `SOP | .raw => `raw))

open quoteSimpConfig (push)
def quoteRingNFConfig (cfg : RingNF.Config) : Option Term := Id.run do
  if cfg == {} then return none
  --  `Quote Bool` fully qualifies true and false but we are trying to generate
  --  the unqualified form here.
  let _inst : Quote Bool := ⟨fun b => mkIdent (if b then `true else `false)⟩
  let a := #[]
    -- skip .red because this is handled by `!` (lean 3 can't write other red settings)
    |> quoteSimpConfig.push cfg {} `recursive (·.recursive)
    |> quoteSimpConfig.push cfg {} `mode (·.mode)
  `({ $[$a:structInstField],* })

def trRingMode : Option Name → M RingNF.RingMode
  | some `SOP | some `horner | none => pure .SOP
  | some `raw => pure .raw
  | some _ => warn! "bad ring mode" | pure .SOP

@[tr_tactic ring_nf] def trRingNF : TacM Syntax.Tactic := do
  let c ← parse (tk "!")?
  let mode ← trRingMode (← parse (ident)?)
  let loc ← trLoc (← parse location)
  let cfg := quoteRingNFConfig { ← parseRingNFConfig (← expr?) with mode }
  match c with
  | none => `(tactic| ring_nf $[(config := $cfg)]? $(loc)?)
  | some _ => `(tactic| ring_nf! $[(config := $cfg)]? $(loc)?)

@[tr_tactic ring] def trRing : TacM Syntax.Tactic := do
  match ← parse (tk "!")? with
  | none => `(tactic| ring)
  | some _ => `(tactic| ring!)

@[tr_tactic ring_exp] def trRingExp : TacM Syntax.Tactic := do
  match ← parse (tk "!")?, ← trLoc (← parse location) with
  | none, none => `(tactic| ring)
  | some _, none => `(tactic| ring!)
  | none, some loc => `(tactic| ring_nf $loc:location)
  | some _, some loc => `(tactic| ring_nf! $loc:location)

@[tr_conv ring_nf] def trRingNFConv : TacM Syntax.Conv := do
  let c ← parse (tk "!")?
  let mode ← trRingMode (← parse (ident)?)
  let cfg := quoteRingNFConfig { ← parseRingNFConfig (← expr?) with mode }
  match c with
  | none => `(conv| ring_nf $[(config := $cfg)]?)
  | some _ => `(conv| ring_nf! $[(config := $cfg)]?)

@[tr_conv ring ring_exp] def trRingConv : TacM Syntax.Conv := do
  match ← parse (tk "!")? with
  | none => `(conv| ring)
  | some _ => `(conv| ring!)
