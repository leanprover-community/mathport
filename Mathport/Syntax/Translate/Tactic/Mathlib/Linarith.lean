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

-- # tactic.linarith
@[trTactic linarith] def trLinarith : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.linarith, "linarith")
  | some _ => (``Parser.Tactic.linarith!, "linarith!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let args := mkNullNode $ ← match ← parse optPExprList with
  | #[] => pure #[]
  | args => return #[mkAtom "[", (mkAtom ",").mkSep $ ← liftM $ args.mapM trExpr, mkAtom "]"]
  let cfg ← mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode tac #[mkAtom s, cfg, o, args]

@[trTactic nlinarith] def trNLinarith : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.nlinarith, "nlinarith")
  | some _ => (``Parser.Tactic.nlinarith!, "nlinarith!")
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let args := mkNullNode $ ← match ← parse optPExprList with
  | #[] => pure #[]
  | args => return #[mkAtom "[", (mkAtom ",").mkSep $ ← liftM $ args.mapM trExpr, mkAtom "]"]
  let cfg ← mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode tac #[mkAtom s, cfg, o, args]

-- # tactic.zify
@[trUserAttr zify] def trZifyAttr := tagAttr `zify

@[trTactic zify] def trZify : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  pure $ mkNode ``Parser.Tactic.zify #[mkAtom "zify", hs, loc]
