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
@[trUserAttr notation_class] def trNotationClassAttr : TacM Syntax := do
  let star := optTk (← parse (tk "*")?).isSome
  let n ← parse (ident)?
  `(attr| notation_class $[*%$star]? $[$(← liftM do n.mapM mkIdentF)]?)

def trSimpsRule : Sum (Name × Name) Name × Bool → M (TSyntax ``Parser.Command.simpsRule)
  | (arg, pfx) => do
    let pfx := optTk pfx
    match arg with
    | .inl (a, b) => `(Parser.Command.simpsRule| $(← mkIdentF a):ident → $(← mkIdentF b) $[as_prefix%$pfx]?)
    | .inr a => `(Parser.Command.simpsRule| - $(← mkIdentF a):ident $[as_prefix%$pfx]?)

@[trUserCmd «initialize_simps_projections»] def trInitializeSimpsProjections : TacM Syntax := do
  let (trc, projs) ← parse do return (← (tk "?")?, ← (return (← ident, ← simpsRules))*)
  let projs ← projs.mapM fun (n, rules) => do
    let rules ← liftM do rules.mapM trSimpsRule
    `(Parser.Command.simpsProj| $(← mkIdentF n):ident ($[$rules],*))
  if trc.isSome then
    `(initialize_simps_projections? $[$projs]*)
  else
    `(initialize_simps_projections $[$projs]*)

@[trUserAttr simps] def trSimpsAttr : TacM Syntax := do
  let (trc, ns, cfg) ← parse $ return (← (tk "?")?, ← ident*, ← (pExpr)?)
  let ns ← liftM $ ns.mapM mkIdentF
  let cfg ← liftM $ cfg.mapM trExpr
  match trc with
  | none => `(attr| simps $[(config := $cfg)]? $[$ns]*)
  | some _ => `(attr| simps? $[(config := $cfg)]? $[$ns]*)
