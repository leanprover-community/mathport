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

-- # number_theory.padics.padic_numbers
@[trTactic padic_index_simp] def trPadicIndexSimp : TacM Syntax := do
  `(tactic| padic_index_simp
    [$(← liftM $ (← parse pExprList).mapM trExpr),*]
    $(← trLoc (← parse location))?)

-- # ring_theory.witt_vector
@[trTactic ghost_fun_tac] def trGhostFunTac : TacM Syntax := do
  `(tactic| ghost_fun_tac $(← trExpr (← parse pExpr)), $(← trExpr (← parse pExpr)))

@[trTactic ghost_calc] def trGhostCalc : TacM Syntax := do
  `(tactic| ghost_calc $[$((← parse ident_*).map trBinderIdent)]*)

@[trTactic init_ring] def trInitRing : TacM Syntax := do
  `(tactic| init_ring $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?)

@[trTactic ghost_simp] def trGhostSimp : TacM Syntax := do
  `(tactic| ghost_simp $[[$((← trSimpArgs (← parse simpArgList)).asNonempty),*]]?)

@[trTactic witt_truncate_fun_tac] def trWittTruncateFunTac : TacM Syntax :=
  `(tactic| witt_truncate_fun_tac)

@[trUserAttr is_poly] def trIsPolyAttr : TacM Syntax := tagAttr `is_poly
