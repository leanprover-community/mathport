/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open Parser

-- # tactic.clear

attribute [tr_tactic clear'] trClear

@[tr_tactic clear_dependent] def trClearDependent : TacM Syntax.Tactic := do
  `(tactic| clear! $[$((← parse ident*).map Lean.mkIdent)]*)

