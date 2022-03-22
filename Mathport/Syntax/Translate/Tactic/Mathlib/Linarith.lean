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
@[trTactic linarith] def trLinarith : TacM Syntax := do
  let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let args := (← (← parse optPExprList).mapM (trExpr ·)).asNonempty
  let cfg ← mkConfigStx? (← (← expr?).mapM (trExpr ·))
  match bang with
  | none => `(tactic| linarith $(cfg)? $[only%$o]? $[[$args,*]]?)
  | some _ => `(tactic| linarith! $(cfg)? $[only%$o]? $[[$args,*]]?)

@[trTactic nlinarith] def trNLinarith : TacM Syntax := do
  let bang ← parse (tk "!")?
  let o := optTk (← parse onlyFlag)
  let args := (← (← parse optPExprList).mapM (trExpr ·)).asNonempty
  let cfg ← mkConfigStx? (← (← expr?).mapM (trExpr ·))
  match bang with
  | none => `(tactic| nlinarith $(cfg)? $[only%$o]? $[[$args,*]]?)
  | some _ => `(tactic| nlinarith! $(cfg)? $[only%$o]? $[[$args,*]]?)

-- # tactic.zify
@[trUserAttr zify] def trZifyAttr := tagAttr `zify

@[trTactic zify] def trZify : TacM Syntax := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  `(tactic| zify $[[$hs,*]]? $(← trLoc (← parse location))?)
