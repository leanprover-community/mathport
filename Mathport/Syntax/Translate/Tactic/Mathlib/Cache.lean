/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Mathlib.Interactive

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.cache

attribute [trTactic unfreezingI] trId
attribute [trTactic resetI] trSkip
attribute [trTactic substI] trSubst
attribute [trTactic casesI] trCases
attribute [trTactic introI] trIntro
attribute [trTactic introsI] trIntros
attribute [trTactic haveI] trHave
attribute [trTactic letI] trLet
attribute [trTactic exactI] trExact
