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

@[tr_user_attr ext] def trExtAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun n => do
  if n.isSome then warn! "unsupported: attribute [ext id]"
  return mkSimpleAttr `ext
  -- This creates a hygienic name, which might be pretty-printed as ext.1:
  -- `(attr| ext)

@[tr_tactic ext1] def trExt1 : TacM Syntax.Tactic := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse (rcasesPat true)*).mapM trRCasesPat
  match hint with
  | none => `(tactic| ext1 $[$pats]*)
  | some _ => `(tactic| ext1? $[$pats]*)

@[tr_tactic ext] def trExt : TacM Syntax.Tactic := do
  let hint ← parse (tk "?")?
  let pats ← liftM $ (← parse rintroPat*).mapM trRIntroPat
  let depth := (← parse (tk ":" *> smallNat)?).map Quote.quote
  match hint with
  | none => `(tactic| ext $[$pats]* $[: $depth]?)
  | some _ => `(tactic| ext? $[$pats]* $[: $depth]?)
