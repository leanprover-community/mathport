/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.suggest

@[tr_tactic suggest] def trSuggest : TacM Syntax.Tactic := do
  let n := (← parse (smallNat)?).map Quote.quote
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let use := (← parse (tk "using" *> ident_*)?).getD #[] |>.map trBinderIdent |>.asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| suggest $[(config := $cfg)]? $(n)? $[[$hs,*]]? $[using $use*]?)

@[tr_tactic library_search] def trLibrarySearch : TacM Syntax.Tactic := do
  let bang ← parse (tk "!")?
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let use := (← parse (tk "using" *> ident_*)?).getD #[] |>.map trIdent_ |>.asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang with
  | none => `(tactic| library_search $[(config := $cfg)]? $[[$hs,*]]? $[using $use,*]?)
  | some _ => `(tactic| library_search! $[(config := $cfg)]? $[[$hs,*]]? $[using $use,*]?)
