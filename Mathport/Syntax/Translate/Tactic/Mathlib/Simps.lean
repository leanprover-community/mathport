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
  let (star, n) ← parse $ return (← (tk "*")?, ← (ident)?)
  pure $ mkNode ``Parser.Attr.notationClass #[mkAtom "notation_class",
    mkOptionalNode' star fun _ => #[mkAtom "*"],
    ← mkOpt n mkIdentF]

def trSimpsRule : Sum (Name × Name) Name × Bool → M Syntax
  | (arg, pfx) => do
    let stx ← match arg with
    | Sum.inl (a, b) => do
      pure $ mkNode ``Parser.Command.simpsRule.rename #[← mkIdentF a, mkAtom "→", ← mkIdentF b]
    | Sum.inr a => do
      pure $ mkNode ``Parser.Command.simpsRule.erase #[mkAtom "-", ← mkIdentF a]
    pure $ mkNode ``Parser.Command.simpsRule #[stx,
      @mkNullNode $ if pfx then #[mkAtom "as_prefix"] else #[]]

@[trUserCmd «initialize_simps_projections»] def trInitializeSimpsProjections : TacM Syntax := do
  let (trc, args) ← parse $ return (← (tk "?")?, ← (return (← ident, ← simpsRules))*)
  let (tac, s) := match trc with
  | none => (``Parser.Command.initializeSimpsProjections, "initialize_simps_projections")
  | some _ => (``Parser.Command.initializeSimpsProjections?, "initialize_simps_projections?")
  pure $ mkNode tac #[mkAtom s, mkNullNode $ ← liftM (m := M) $ args.mapM fun (n, rules) =>
    return mkNode ``Parser.Command.simpsProj #[← mkIdentF n,
      mkNullNode $ ← match rules with
      | #[] => pure #[]
      | _ => return #[mkAtom "(", (mkAtom ",").mkSep $ ← rules.mapM trSimpsRule, mkAtom ")"]]]

@[trUserAttr simps] def trSimpsAttr : TacM Syntax := do
  let (trc, ns, cfg) ← parse $ return (← (tk "?")?, ← ident*, ← (pExpr)?)
  let ns ← liftM $ ns.mapM mkIdentF
  let cfg ← liftM $ cfg.mapM trExpr
  match trc with
  | none => `(attr| simps $[(config := $cfg)]? $ns*)
  | some _ => `(attr| simps? $[(config := $cfg)]? $ns*)
