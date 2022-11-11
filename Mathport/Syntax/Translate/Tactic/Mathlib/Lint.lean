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

-- # tactic.lint

@[tr_user_attr nolint] def trNolintAttr : Parse1 Syntax.Attr :=
  parse1 ident* fun n => `(attr| nolint $(n.map mkIdent)*)

@[tr_user_attr linter] def trLinterAttr := tagAttr `linter

@[tr_user_cmd «#lint»] def trLintCmd : Parse1 Syntax.Command :=
  parse1 lintArgs fun ((_fast, _verb), _use_only, _extra) =>
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint)

@[tr_user_cmd «#lint_mathlib»] def trLintMathlibCmd : Parse1 Syntax.Command :=
  parse1 lintArgs fun ((_fast, _verb), _use_only, _extra) =>
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint mathlib)

@[tr_user_cmd «#lint_all»] def trLintAllCmd : Parse1 Syntax.Command :=
  parse1 lintArgs fun ((_fast, _verb), _use_only, _extra) =>
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint all)

@[tr_user_cmd «#list_linters»] def trListLintersCmd : Parse1 Syntax.Command :=
  parse0 `(command| #list_linters)
