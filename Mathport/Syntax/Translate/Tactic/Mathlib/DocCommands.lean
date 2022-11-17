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

-- # tactic.doc_commands

@[tr_user_cmd «copy_doc_string»] def trCopyDocString : Parse1 Unit :=
  parse1 (return (← ident, ← tk "->" *> ident*)) fun (fr, to_) => do
  unless to_.isEmpty do
    pushM `(command| attribute [inherit_doc $(← mkIdentI fr)] $(← liftM $ to_.mapM mkIdentI)*)

@[tr_user_cmd «library_note»] def trLibraryNote (doc : Option String) : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do
  let ⟨_, Expr.string s⟩ := e | warn! "unsupported: weird string"
  `(command| library_note $(Syntax.mkStrLit s) $(trDocComment doc.get!):docComment)

@[tr_user_cmd «add_tactic_doc»] def trAddTacticDoc (doc : Option String) : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do
  `(command| $[$(doc.map trDocComment)]? add_tactic_doc $(← trExpr e))

@[tr_user_cmd «add_decl_doc»] def trAddDeclDoc (doc : Option String) : Parse1 Syntax.Command :=
  parse1 ident fun n => do
  `(command| $(trDocComment doc.get!):docComment add_decl_doc $(← mkIdentI n))
