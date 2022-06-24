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

-- # tactic.squeeze

@[trTactic squeeze_scope] def trSqueezeScope : TacM Syntax := do
  `(tactic| squeeze_scope $(← trBlock (← itactic)):tacticSeq)

@[trTactic squeeze_simp] def trSqueezeSimp : TacM Syntax := do
  let ques ← parse_0 $ parse (tk "?")?; let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let loc ← trLoc (← parse location)
  let (cfg, disch) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  let rest ← `(Lean.Parser.Tactic.squeezeSimpArgsRest|
    $[$cfg:config]? $(disch)? $[only%$o]? $[[$hs,*]]? $[with $attrs*]? $[$loc:location]?)
  match ques, bang with
  | none, none => `(tactic| squeeze_simp $rest)
  | none, some _ => `(tactic| squeeze_simp? $rest)
  | some _, none => `(tactic| squeeze_simp! $rest)
  | some _, some _ => `(tactic| squeeze_simp!? $rest)

@[trTactic squeeze_simpa] def trSqueezeSimpa : TacM Syntax := do
  let ques ← parse_0 $ parse (tk "?")?; let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let (cfg, disch) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  let rest ← `(Mathlib.Tactic.simpaArgsRest|
    $[$cfg:config]? $(disch)? $[only%$o]? $[[$hs,*]]? $[with $attrs*]? $[using $e]?)
  match ques, bang with
  | none, none => `(tactic| squeeze_simpa $rest)
  | none, some _ => `(tactic| squeeze_simpa? $rest)
  | some _, none => `(tactic| squeeze_simpa! $rest)
  | some _, some _ => `(tactic| squeeze_simpa!? $rest)

@[trTactic squeeze_dsimp] def trSqueezeDSimp : TacM Syntax := do
  let ques ← parse_0 $ parse (tk "?")?; let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let loc ← trLoc (← parse location)
  let (cfg, _) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  let rest ← `(Lean.Parser.Tactic.squeezeDSimpArgsRest|
    $[$cfg:config]? $[only%$o]? $[[$hs,*]]? $[with $attrs*]? $[$loc:location]?)
  match ques, bang with
  | none, none => `(tactic| squeeze_dsimp $rest)
  | none, some _ => `(tactic| squeeze_dsimp? $rest)
  | some _, none => `(tactic| squeeze_dsimp! $rest)
  | some _, some _ => `(tactic| squeeze_dsimp!? $rest)
