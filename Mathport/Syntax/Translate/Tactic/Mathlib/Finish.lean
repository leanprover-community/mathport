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

-- # tactic.finish

def trUsingList (args : Array (Spanned AST3.Expr)) : M Syntax :=
  @mkNullNode <$> match args with
  | #[] => pure #[]
  | args => return #[mkAtom "using", (mkAtom ",").mkSep $ ← args.mapM trExpr]

@[trTactic clarify] def trClarify : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let ps ← trUsingList $ (← parse (tk "using" *> pExprListOrTExpr)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode ``Parser.Tactic.clarify #[mkAtom "clarify", ← mkConfigStx cfg, hs, ps]

@[trTactic safe] def trSafe : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let ps ← trUsingList $ (← parse (tk "using" *> pExprListOrTExpr)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode ``Parser.Tactic.safe #[mkAtom "safe", ← mkConfigStx cfg, hs, ps]

@[trTactic finish] def trFinish : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let ps ← trUsingList $ (← parse (tk "using" *> pExprListOrTExpr)?).getD #[]
  let cfg ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode ``Parser.Tactic.finish #[mkAtom "finish", ← mkConfigStx cfg, hs, ps]
