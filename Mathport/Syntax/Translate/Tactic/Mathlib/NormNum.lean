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
@[trUserAttr norm_num] def trNormNumAttr := tagAttr `norm_num

@[trTactic norm_num1] def trNormNum1 : TacM Syntax := do
  `(tactic| norm_num1 $(← trLoc (← parse location))?)

@[trTactic norm_num] def trNormNum : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let loc := mkOptionalNode $ ← trLoc (← parse location)
  pure $ mkNode ``Tactic.normNum #[mkAtom "norm_num", hs, loc]

@[trTactic apply_normed] def trApplyNormed : TacM Syntax := do
  `(tactic| apply_normed $(← trExpr (← parse pExpr)))

@[trConv norm_num1] def trNormNum1Conv : TacM Syntax := `(conv| norm_num1)

@[trConv norm_num] def trNormNumConv : TacM Syntax := do
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  pure $ mkNode ``Parser.Tactic.Conv.normNum #[mkAtom "norm_num", hs]
