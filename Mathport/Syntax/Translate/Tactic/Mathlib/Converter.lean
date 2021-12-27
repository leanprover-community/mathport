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

-- # tactic.converter

@[trTactic old_conv] def trOldConv : TacM Syntax := do
  warn! "unsupported tactic old_conv" -- unattested

@[trTactic find] def trFindTac : TacM Syntax := do
  warn! "unsupported tactic find" -- unattested

@[trTactic conv_lhs] def trConvLHS : TacM Syntax := do
  `(tactic| conv_lhs
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr)]?
    => $(← trConvBlock (← itactic)):convSeq)

@[trTactic conv_rhs] def trConvRHS : TacM Syntax := do
  `(tactic| conv_rhs
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr)]?
    => $(← trConvBlock (← itactic)):convSeq)

@[trConv erw] def trERwConv : TacM Syntax := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  if let some cfg ← expr? then
    warn! "warning: unsupported: erw with cfg: {repr cfg}"
  `(conv| erw [$q,*])

@[trConv apply_congr] def trApplyCongr : TacM Syntax := do
  `(conv| apply_congr $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

