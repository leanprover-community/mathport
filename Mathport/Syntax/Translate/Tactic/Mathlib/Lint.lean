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

@[trUserAttr nolint] def trNolintAttr : Parse1 Syntax :=
  parse1 ident* fun n => `(attr| nolint $(n.map mkIdent)*)

@[trUserAttr linter] def trLinterAttr := tagAttr `linter

@[trUserCmd «#lint»] def trLintCmd : Parse1 Syntax :=
  parse1 lintArgs fun ((_fast, _verb), _use_only, _extra) =>
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint)

@[trUserCmd «#lint_mathlib»] def trLintMathlibCmd : Parse1 Syntax :=
  parse1 lintArgs fun ((_fast, _verb), _use_only, _extra) =>
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint mathlib)

@[trUserCmd «#lint_all»] def trLintAllCmd : Parse1 Syntax :=
  parse1 lintArgs fun ((_fast, _verb), _use_only, _extra) =>
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint all)

@[trUserCmd «#list_linters»] def trListLintersCmd : Parse1 Syntax :=
  parse0 `(command| #list_linters)
