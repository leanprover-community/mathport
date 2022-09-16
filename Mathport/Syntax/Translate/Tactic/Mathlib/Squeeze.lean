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
  let _ques ← parse_0 $ parse (tk "?")?; let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent
  let hs := hs ++ attrs.map (·)
  let hs := hs.asNonempty
  let loc ← trLoc (← parse location)
  let (cfg, disch) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  let rest ← `(Lean.Parser.Tactic.simpTraceArgsRest|
    $[$cfg:config]? $(disch)? $[only%$o]? $[[$hs,*]]? $[$loc:location]?)
  if bang.isSome then `(tactic| simp?! $rest) else `(tactic| simp? $rest)

@[trTactic squeeze_simpa] def trSqueezeSimpa : TacM Syntax := do
  let _ques ← parse_0 $ parse (tk "?")?; let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent
  let hs := hs ++ attrs.map (·)
  let hs := hs.asNonempty
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let (cfg, disch) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  let rest ← `(Std.Tactic.simpaArgsRest|
    $[$cfg:config]? $(disch)? $[only%$o]? $[[$hs,*]]? $[using $e]?)
  if bang.isSome then `(tactic| simpa?! $rest) else `(tactic| simpa? $rest)

@[trTactic squeeze_dsimp] def trSqueezeDSimp : TacM Syntax := do
  let _ques ← parse_0 $ parse (tk "?")?; let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let (hs, all) := filterSimpStar hs
  if all then warn! "unsupported squeeze_dsimp [*]"
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent
  let hs := hs ++ attrs.map (·)
  let hs := hs.asNonempty
  let loc ← trLoc (← parse location)
  let (cfg, _) ← parseSimpConfig <| (← parse (structInst)?).map Spanned.dummy
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  let rest ← `(Lean.Parser.Tactic.dsimpTraceArgsRest|
    $[$cfg:config]? $[only%$o]? $[[$hs,*]]? $[$loc:location]?)
  if bang.isSome then `(tactic| dsimp?! $rest) else `(tactic| dsimp? $rest)
