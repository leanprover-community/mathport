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

@[trUserAttr nolint] def trNolintAttr : TacM Syntax := do
  `(attr| nolint $((← parse ident*).map mkIdent)*)

@[trUserAttr linter] def trLinterAttr := tagAttr `linter

@[trUserCmd «#lint»] def trLintCmd : TacM Syntax := do
  let ((_fast, _verb), _use_only, _extra) ← parse lintArgs
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint)

@[trUserCmd «#lint_mathlib»] def trLintMathlibCmd : TacM Syntax := do
  let ((_fast, _verb), _use_only, _extra) ← parse lintArgs
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint mathlib)

@[trUserCmd «#lint_all»] def trLintAllCmd : TacM Syntax := do
  let ((_fast, _verb), _use_only, _extra) ← parse lintArgs
  -- TODO: translate (hard because syntax quotation is tricky)
  `(#lint all)

@[trUserCmd «#list_linters»] def trListLintersCmd : TacM Syntax :=
  parse_0 `(command| #list_linters)
