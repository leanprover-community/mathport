/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean

namespace Mathport.Translate.Tactic
open Parser

-- # tactic.simps
@[tr_user_attr notation_class] def trNotationClassAttr : Parse1 Syntax.Attr :=
  parse1 (return (← (tk "*")?, ← (ident)?)) fun (star, n) => do
  let star := optTk star.isSome
  `(attr| notation_class $[*%$star]? $[$(← liftM do n.mapM mkIdentF)]?)

def trSimpsRule : Sum (Name × Name) Name × Bool → M (Array (TSyntax ``Parser.Command.simpsRule))
  | (arg, pfx) => do
    let (rhs, rule) ← match arg with
      | .inl (a, b) =>
        let rhs ← mkIdentF b
        Prod.mk rhs <$> `(Parser.Command.simpsRule| $(← mkIdentF a):ident → $rhs)
      | .inr a =>
        let rhs ← mkIdentF a
        Prod.mk rhs <$> `(Parser.Command.simpsRule| - $rhs)
    if pfx then return #[rule, ← `(Parser.Command.simpsRule| as_prefix $rhs)] else return #[rule]

@[tr_user_cmd «initialize_simps_projections»] def trInitializeSimpsProjections : Parse1 Unit :=
  parse1 (return (← (tk "?")?, ← (return (← ident, ← simpsRules))*)) fun (trc, projs) => do
    for (n, rules) in projs do
      let rules ← liftM do rules.concatMapM trSimpsRule
      if trc.isSome then
        pushM `(initialize_simps_projections? $(← mkIdentF n):ident ($[$rules],*))
      else
        pushM `(initialize_simps_projections $(← mkIdentF n):ident ($[$rules],*))

@[tr_user_attr simps] def trSimpsAttr : Parse1 Syntax.Attr :=
  parse1 (return (← (tk "?")?, ← ident*, ← (pExpr)?)) fun (trc, ns, cfg) => do
  let ns ← liftM $ ns.mapM mkIdentF
  let cfg ← liftM $ cfg.mapM trExpr
  match trc with
  | none => `(attr| simps $[(config := $cfg)]? $[$ns]*)
  | some _ => `(attr| simps? $[(config := $cfg)]? $[$ns]*)
