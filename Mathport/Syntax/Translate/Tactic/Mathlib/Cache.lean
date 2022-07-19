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

attribute [trTactic unfreezingI] trId
attribute [trTactic resetI] trSkip
attribute [trTactic substI] trSubst
attribute [trTactic casesI] trCases
attribute [trTactic introI] trIntro
attribute [trTactic introsI] trIntros
attribute [trTactic exactI] trExact

@[trTactic «haveI»] def trHaveI : TacM Syntax := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| haveI $[$h:ident]? $[: $ty:term]? := $(← trExpr pr))
  | none => `(tactic| have $[$h:ident]? $[: $ty:term]?)

@[trTactic «letI»] def trLetI : TacM Syntax := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => match h with
    | some h => `(tactic| letI $h:ident $[: $ty:term]? := $(← trExpr pr))
    | none => `(tactic| letI $[: $ty:term]? := $(← trExpr pr))
  | none =>
    `(tactic| let $[$h:ident]? $[: $ty:term]?)
