/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Mathlib.Interactive

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3
open Translate.Parser

-- # tactic.cache

attribute [tr_tactic unfreezingI] trId
attribute [tr_tactic resetI] trSkip
attribute [tr_tactic substI] trSubst
attribute [tr_tactic casesI] trCases
attribute [tr_tactic introI] trIntro
attribute [tr_tactic introsI] trIntros
attribute [tr_tactic exactI] trExact

@[tr_tactic «haveI»] def trHaveI : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| haveI $[$h:ident]? $[: $ty:term]? := $(← trExpr pr))
  | none => `(tactic| have $[$h:ident]? $[: $ty:term]?)

@[tr_tactic «letI»] def trLetI : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => match h with
    | some h => `(tactic| letI $h:ident $[: $ty:term]? := $(← trExpr pr))
    | none => `(tactic| letI $[: $ty:term]? := $(← trExpr pr))
  | none =>
    `(tactic| let $[$h:ident]? $[: $ty:term]?)
