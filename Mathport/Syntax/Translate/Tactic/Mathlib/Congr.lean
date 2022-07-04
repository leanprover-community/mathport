/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3
import Mathport.Syntax.Translate.Tactic.Mathlib.RCases

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.congr
@[trTactic congr'] def trCongr' : TacM Syntax := do
  let n ← parse (smallNat)?
  let args ← parse (tk "with" *> return (← (rcasesPat true)*, ← (tk ":" *> smallNat)?))?
  let pats ← args.mapM (liftM do ·.1.mapM trRCasesPat)
  let ks := args.map (·.2.map quote)
  `(tactic| congr $[$(n.map quote)]? $[with $[$pats]* $[: $ks]?]?)

@[trTactic rcongr] def trRCongr : TacM Syntax := do
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  `(tactic| rcongr $[$pats]*)

@[trTactic convert] def trConvert : TacM Syntax := do
  let sym := optTk (← parse (tk "<-")?).isSome
  let r ← trExpr (← parse pExpr)
  let n ← parse (tk "using" *> smallNat)?
  `(tactic| convert $[←%$sym]? $r $[using $(n.map quote)]?)

@[trTactic convert_to] def trConvertTo : TacM Syntax := do
  `(tactic| convert_to $(← trExpr (← parse pExpr))
    $[using $((← parse (tk "using" *> smallNat)?).map Quote.quote)]?)

@[trTactic ac_change] def trAcChange : TacM Syntax := do
  `(tactic| ac_change $(← trExpr (← parse pExpr))
    $[using $((← parse (tk "using" *> smallNat)?).map Quote.quote)]?)


