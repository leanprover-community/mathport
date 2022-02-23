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

-- # tactic.suggest
def trSuggestUsing (args : Array BinderName) : Syntax :=
  mkNullNode $ match args with
  | #[] => #[]
  | _ => #[mkAtom "using", mkNullNode (args.map trBinderIdent)]

@[trTactic suggest] def trSuggest : TacM Syntax := do
  let n := (← parse (smallNat)?).map Quote.quote
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let use := trSuggestUsing ((← parse (tk "using" *> ident_*)?).getD #[])
  let cfg ← mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode ``Parser.Tactic.suggest #[mkAtom "suggest", cfg, hs, trSimpAttrs attrs, use]

@[trTactic library_search] def trLibrarySearch : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Tactic.LibrarySearch.librarySearch', "library_search")
  | some _ => (``Tactic.LibrarySearch.librarySearch!, "library_search!")
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let use := trSuggestUsing ((← parse (tk "using" *> ident_*)?).getD #[])
  let cfg ← mkConfigStx $ ← liftM $ (← expr?).mapM trExpr
  pure $ mkNode tac #[mkAtom s, cfg, hs, trSimpAttrs attrs, use]
