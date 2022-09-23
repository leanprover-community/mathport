/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.hint

@[trUserAttr hint_tactic] def trHintAttr := tagAttr `hint_tactic

@[trUserCmd «add_hint_tactic»] def trAddHintTactic : Parse1 Syntax :=
  parse1 (pExpr *> withInput pExpr) fun (e, _) => do
  let tac ← match e with
  | ⟨_, Expr.«`[]» tacs⟩ => trIdTactic ⟨false, none, none, tacs⟩
  | _ => warn! "unsupported (impossible)"
  `(command| add_hint_tactic $tac)

@[trTactic hint] def trHint : TacM Syntax := `(tactic| hint)
