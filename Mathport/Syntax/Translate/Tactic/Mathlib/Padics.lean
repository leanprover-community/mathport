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
@[tr_tactic padic_index_simp] def trPadicIndexSimp : TacM Syntax.Tactic := do
  `(tactic| padic_index_simp
    [$(← liftM $ (← parse pExprList).mapM trExpr),*]
    $(← trLoc (← parse location))?)

-- # ring_theory.witt_vector
@[tr_tactic ghost_fun_tac] def trGhostFunTac : TacM Syntax.Tactic := do
  `(tactic| ghost_fun_tac $(← trExpr (← parse pExpr)), $(← trExpr (← parse pExpr)))

@[tr_tactic ghost_calc] def trGhostCalc : TacM Syntax.Tactic := do
  `(tactic| ghost_calc $[$((← parse ident_*).map trBinderIdent)]*)

@[tr_tactic init_ring] def trInitRing : TacM Syntax.Tactic := do
  `(tactic| init_ring $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?)

@[tr_tactic ghost_simp] def trGhostSimp : TacM Syntax.Tactic := do
  `(tactic| ghost_simp $[[$((← trSimpArgs (← parse simpArgList)).asNonempty),*]]?)

@[tr_tactic witt_truncate_fun_tac] def trWittTruncateFunTac : TacM Syntax.Tactic :=
  `(tactic| witt_truncate_fun_tac)

@[tr_user_attr is_poly] def trIsPolyAttr := tagAttr `is_poly
