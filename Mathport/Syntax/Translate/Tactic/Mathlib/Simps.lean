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
@[tr_user_attr notation_class] def trNotationClassAttr : Parse1 Syntax :=
  parse1 (return (← (tk "*")?, ← (ident)?)) fun (star, n) => do
  let star := optTk star.isSome
  `(attr| notation_class $[*%$star]? $[$(← liftM do n.mapM mkIdentF)]?)

def trSimpsRule : Sum (Name × Name) Name × Bool → M (TSyntax ``Parser.Command.simpsRule)
  | (arg, pfx) => do
    let pfx := optTk pfx
    match arg with
    | .inl (a, b) => `(Parser.Command.simpsRule| $(← mkIdentF a):ident → $(← mkIdentF b) $[as_prefix%$pfx]?)
    | .inr a => `(Parser.Command.simpsRule| - $(← mkIdentF a):ident $[as_prefix%$pfx]?)

@[tr_user_cmd «initialize_simps_projections»] def trInitializeSimpsProjections : Parse1 Syntax :=
  parse1 (return (← (tk "?")?, ← (return (← ident, ← simpsRules))*)) fun (trc, projs) => do
  let projs ← projs.mapM fun (n, rules) => do
    let rules ← liftM do rules.mapM trSimpsRule
    `(Parser.Command.simpsProj| $(← mkIdentF n):ident ($[$rules],*))
  if trc.isSome then
    `(initialize_simps_projections? $[$projs]*)
  else
    `(initialize_simps_projections $[$projs]*)

@[tr_user_attr simps] def trSimpsAttr : Parse1 Syntax :=
  parse1 (return (← (tk "?")?, ← ident*, ← (pExpr)?)) fun (trc, ns, cfg) => do
  let ns ← liftM $ ns.mapM mkIdentF
  let cfg ← liftM $ cfg.mapM trExpr
  match trc with
  | none => `(attr| simps $[(config := $cfg)]? $[$ns]*)
  | some _ => `(attr| simps? $[(config := $cfg)]? $[$ns]*)
