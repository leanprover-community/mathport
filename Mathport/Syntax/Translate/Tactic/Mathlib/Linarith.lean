/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.linarith
@[tr_tactic linarith] def trLinarith : TacM Syntax.Tactic := do
  let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let args := (← (← parse optPExprList).mapM (trExpr ·)).asNonempty
  let cfg ← mkConfigStx? (← (← expr?).mapM (trExpr ·))
  match bang with
  | none => `(tactic| linarith $(cfg)? $[only%$o]? $[[$args,*]]?)
  | some _ => `(tactic| linarith! $(cfg)? $[only%$o]? $[[$args,*]]?)

@[tr_tactic nlinarith] def trNLinarith : TacM Syntax.Tactic := do
  let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let args := (← (← parse optPExprList).mapM (trExpr ·)).asNonempty
  let cfg ← mkConfigStx? (← (← expr?).mapM (trExpr ·))
  match bang with
  | none => `(tactic| nlinarith $(cfg)? $[only%$o]? $[[$args,*]]?)
  | some _ => `(tactic| nlinarith! $(cfg)? $[only%$o]? $[[$args,*]]?)

-- # tactic.zify
@[tr_user_attr zify] def trZifyAttr := tagAttr `zify

@[tr_tactic zify] def trZify : TacM Syntax.Tactic := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  `(tactic| zify $[[$hs,*]]? $(← trLoc (← parse location))?)

-- # tactic.qify
@[tr_user_attr qify] def trQifyAttr := tagAttr `qify

@[tr_tactic qify] def trQify : TacM Syntax.Tactic := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  `(tactic| qify $[[$hs,*]]? $(← trLoc (← parse location))?)

-- # tactic.polyrith
@[tr_tactic polyrith] def trPolyrith : TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let args := (← (← parse optPExprList).mapM (trExpr ·)).asNonempty
  `(tactic| polyrith $[only%$o]? $[[$args,*]]?)
