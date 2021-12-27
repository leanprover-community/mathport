/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Mathlib.RCases

open Lean

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.ext

@[trUserAttr ext] def trExtAttr : TacM Syntax := do
  `(attr| ext $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trTactic ext1] def trExt1 : TacM Syntax := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  match hint with
  | none => `(tactic| ext1 $pats*)
  | some _ => `(tactic| ext1? $pats*)

@[trTactic ext] def trExt : TacM Syntax := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  let depth := (← parse (tk ":" *> smallNat)?).map Quote.quote
  match hint with
  | none => `(tactic| ext $pats* $[: $depth]?)
  | some _ => `(tactic| ext? $pats* $[: $depth]?)
