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

-- # tactic.simpa

def trSimpaCore (autoUnfold trace : Bool) (parseCfg : TacM (Option (Spanned AST3.Expr))) :
    TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let (cfg, disch) ← parseSimpConfig (← parseCfg)
  let cfg ← mkConfigStx? (cfg.bind quoteSimpConfig)
  let rest ← `(Std.Tactic.Simpa.simpaArgsRest|
    $[$cfg:config]? $(disch)? $[only%$o]? $[[$hs,*]]? $[using $e]?)
  match autoUnfold, trace with
  | true, true => `(tactic| simpa?! $rest)
  | false, true => `(tactic| simpa? $rest)
  | true, false => `(tactic| simpa! $rest)
  | false, false => `(tactic| simpa $rest)

@[tr_tactic simpa] def trSimpa : TacM Syntax.Tactic := do
  let unfold ← parse (tk "!")?; let squeeze ← parse (tk "?")?
  trSimpaCore unfold.isSome squeeze.isSome expr?

-- # tactic.squeeze

@[tr_tactic squeeze_scope] def trSqueezeScope : TacM Syntax.Tactic := do
  `(tactic| squeeze_scope $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic squeeze_simp] def trSqueezeSimp : TacM Syntax.Tactic := do
  let _ques ← parse (pure ()) <* parse (tk "?")?; let bang ← parse (tk "!")?
  trSimpCore bang.isSome true

@[tr_tactic squeeze_simpa] def trSqueezeSimpa : TacM Syntax.Tactic := do
  let _ques ← parse (pure ()) <* parse (tk "?")?; let bang ← parse (tk "!")?
  trSimpaCore bang.isSome true expr?

@[tr_tactic squeeze_dsimp] def trSqueezeDSimp : TacM Syntax.Tactic := do
  let _ques ← parse (pure ()) <* parse (tk "?")?; let bang ← parse (tk "!")?
  trDSimpCore bang.isSome true (return (← parse (structInst)?).map .dummy)
