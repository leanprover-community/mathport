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

-- # tactic.norm_num
@[tr_user_attr norm_num] def trNormNumAttr := tagAttr `norm_num

@[tr_tactic norm_num1] def trNormNum1 : TacM Syntax.Tactic := do
  `(tactic| norm_num1 $(← trLoc (← parse location))?)

@[tr_tactic norm_num] def trNormNum : TacM Syntax.Tactic := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let loc ← trLoc (← parse location)
  `(tactic| norm_num $[[$hs,*]]? $(loc)?)

@[tr_tactic apply_normed] def trApplyNormed : TacM Syntax.Tactic := do
  `(tactic| apply_normed $(← trExpr (← parse pExpr)))

@[tr_conv norm_num1] def trNormNum1Conv : TacM Syntax.Conv := `(conv| norm_num1)

@[tr_conv norm_num] def trNormNumConv : TacM Syntax.Conv := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  `(conv| norm_num $[[$hs,*]]?)

@[tr_user_cmd «#norm_num»] def trNormNumCmd : Parse1 Syntax.Command :=
  parse1 (return (← onlyFlag, ← simpArgList,
    (← (tk "with" *> ident*)?).getD #[], ← (tk ":")? *> pExpr))
  fun (o, args, attrs, e) => do
    let o := optTk o
    let hs ← trSimpArgs args
    let hs := (hs ++ attrs.map trSimpExt).asNonempty
    `(command| #norm_num $[only%$o]? $[[$hs,*]]? $(← trExpr e))
