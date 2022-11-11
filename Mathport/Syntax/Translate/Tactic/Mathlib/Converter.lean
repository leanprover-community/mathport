/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open Mathport.Translate.Parser

-- # tactic.converter

@[tr_tactic old_conv] def trOldConv : TacM Syntax.Tactic := do
  warn! "unsupported tactic old_conv" -- unattested

@[tr_tactic find] def trFindTac : TacM Syntax.Tactic := do
  warn! "unsupported tactic find" -- unattested

@[tr_tactic conv_lhs] def trConvLHS : TacM Syntax.Tactic := do
  `(tactic| conv_lhs
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr):term]?
    => $(← trConvBlock (← itactic)):convSeq)

@[tr_tactic conv_rhs] def trConvRHS : TacM Syntax.Tactic := do
  `(tactic| conv_rhs
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr):term]?
    => $(← trConvBlock (← itactic)):convSeq)

@[tr_conv erw] def trERwConv : TacM Syntax.Conv := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  if let some cfg ← expr? then
    warn! "warning: unsupported: erw with cfg: {repr cfg}"
  `(conv| erw [$q,*])

@[tr_conv apply_congr] def trApplyCongr : TacM Syntax.Conv := do
  `(conv| apply_congr $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

