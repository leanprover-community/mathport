/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.cache

@[trTactic unfreezingI] def trUnfreezingI : TacM Syntax := do
  `(tactic| ($(← trBlock (← itactic)):tacticSeq))

@[trTactic resetI] def trResetI : TacM Syntax := `(tactic| skip)

@[trTactic substI] def trSubstI : TacM Syntax := do
  `(tactic| subst $(← trExpr (← parse pExpr)))

def trWithIdentList : Array BinderName → Option (Array Syntax)
  | #[] => none
  | ids => some (ids.map trBinderIdent)

@[trTactic casesI] def trCasesI : TacM Syntax := do
  let (hp, e) ← parse casesArg
  `(tactic| cases' $[$(hp.map mkIdent) :]?
    $(← trExpr e) $[with $(trWithIdentList (← parse withIdentList))*]?)

@[trTactic introI] def trIntroI : TacM Syntax := do
  match ← parse ident_ ? with
  | some (BinderName.ident h) => `(tactic| intro $(mkIdent h):ident)
  | _ => `(tactic| intro)

@[trTactic introsI] def trIntrosI : TacM Syntax := do
  match ← parse ident_* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intros $(hs.map trIdent_)*)

@[trTactic haveI] def trHaveI : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| have $[$h:ident]? $[: $ty:term]? := $(← trExpr pr))
  | none => `(tactic| have $[$h:ident]? $[: $ty:term]?)

@[trTactic letI] def trLetI : TacM Syntax := do
  let h ← parse (ident)?
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    -- FIXME: this is a keyword now
    `(tactic| let $(mkIdent <| h.getD `this') $[: $ty:term]? := $(← trExpr pr))
  | none =>
    `(tactic| let $[$(h.map mkIdent):ident]? $[: $ty:term]?)

@[trTactic exactI] def trExactI : TacM Syntax := do
  `(tactic| exact $(← trExpr (← parse pExpr)))
