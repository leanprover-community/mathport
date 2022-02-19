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

-- # tactic.squeeze

@[trTactic squeeze_scope] def trSqueezeScope : TacM Syntax := do
  `(tactic| squeeze_scope $(← trBlock (← itactic)):tacticSeq)

@[trTactic squeeze_simp] def trSqueezeSimp : TacM Syntax := do
  let (tac, s) := match ← parse_0 $ parse (tk "?")?, ← parse (tk "!")? with
  | none, none => (``Parser.Tactic.squeezeSimp, "squeeze_simp")
  | none, some _ => (``Parser.Tactic.squeezeSimp?, "squeeze_simp?")
  | some _, none => (``Parser.Tactic.squeezeSimp!, "squeeze_simp!")
  | some _, some _ => (``Parser.Tactic.squeezeSimp?!, "squeeze_simp?!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  let (cfg, disch) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx $ cfg.bind quoteSimpConfig
  pure $ mkNode tac #[mkAtom s, cfg, disch, o, hs, trSimpAttrs attrs, loc]

@[trTactic squeeze_simpa] def trSqueezeSimpa : TacM Syntax := do
  let (tac, s) := match ← parse_0 $ parse (tk "?")?, ← parse (tk "!")? with
  | none, none => (``Parser.Tactic.squeezeSimpa, "squeeze_simpa")
  | none, some _ => (``Parser.Tactic.squeezeSimpa?, "squeeze_simpa?")
  | some _, none => (``Parser.Tactic.squeezeSimpa!, "squeeze_simpa!")
  | some _, some _ => (``Parser.Tactic.squeezeSimpa?!, "squeeze_simpa?!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let (cfg, disch) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx $ cfg.bind quoteSimpConfig
  pure $ mkNode tac #[mkAtom s, cfg, disch, o, hs, trSimpAttrs attrs,
    mkOptionalNode' e fun e => #[mkAtom "using", e]]

@[trTactic squeeze_dsimp] def trSqueezeDSimp : TacM Syntax := do
  let (tac, s) := match ← parse_0 $ parse (tk "?")?, ← parse (tk "!")? with
  | none, none => (``Parser.Tactic.squeezeDSimp, "squeeze_dsimp")
  | none, some _ => (``Parser.Tactic.squeezeDSimp?, "squeeze_dsimp?")
  | some _, none => (``Parser.Tactic.squeezeDSimp!, "squeeze_dsimp!")
  | some _, some _ => (``Parser.Tactic.squeezeDSimp?!, "squeeze_dsimp?!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  let (cfg, _) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx $ cfg.bind quoteSimpConfig
  pure $ mkNode tac #[mkAtom s, cfg, o, hs, trSimpAttrs attrs, loc]
