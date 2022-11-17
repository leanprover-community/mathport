/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.solve_by_elim

@[tr_tactic apply_assumption] def trApplyAssumption : TacM Syntax.Tactic := do
  match ← parse (pExprList)?, ← expr?, ← expr? with
  | none, none, none => `(tactic| apply_assumption)
  | _, _, _ => warn! "unsupported: apply_assumption arguments" -- unattested

@[tr_tactic solve_by_elim] def trSolveByElim : TacM Syntax.Tactic := do
  let star := optTk (← parse (tk "*")?).isSome
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let cfg ← mkConfigStx? (← liftM $ (← expr?).mapM trExpr)
  `(tactic| solve_by_elim $[*%$star]? $(cfg)? $[only%$o]? $[[$hs,*]]?)
