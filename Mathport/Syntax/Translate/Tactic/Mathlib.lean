/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3
import Mathport.Syntax.Translate.Tactic.Mathlib.Alias
import Mathport.Syntax.Translate.Tactic.Mathlib.Apply
import Mathport.Syntax.Translate.Tactic.Mathlib.Cache
import Mathport.Syntax.Translate.Tactic.Mathlib.Choose
import Mathport.Syntax.Translate.Tactic.Mathlib.Clear
import Mathport.Syntax.Translate.Tactic.Mathlib.Congr
import Mathport.Syntax.Translate.Tactic.Mathlib.Converter
import Mathport.Syntax.Translate.Tactic.Mathlib.Core
import Mathport.Syntax.Translate.Tactic.Mathlib.DocCommands
import Mathport.Syntax.Translate.Tactic.Mathlib.Ext
import Mathport.Syntax.Translate.Tactic.Mathlib.Finish
import Mathport.Syntax.Translate.Tactic.Mathlib.Hint
import Mathport.Syntax.Translate.Tactic.Mathlib.Interactive
import Mathport.Syntax.Translate.Tactic.Mathlib.Linarith
import Mathport.Syntax.Translate.Tactic.Mathlib.Lint
import Mathport.Syntax.Translate.Tactic.Mathlib.Misc1
import Mathport.Syntax.Translate.Tactic.Mathlib.Misc2
import Mathport.Syntax.Translate.Tactic.Mathlib.Monotonicity
import Mathport.Syntax.Translate.Tactic.Mathlib.NormCast
import Mathport.Syntax.Translate.Tactic.Mathlib.NormNum
import Mathport.Syntax.Translate.Tactic.Mathlib.Padics
import Mathport.Syntax.Translate.Tactic.Mathlib.RCases
import Mathport.Syntax.Translate.Tactic.Mathlib.Ring
import Mathport.Syntax.Translate.Tactic.Mathlib.Simps
import Mathport.Syntax.Translate.Tactic.Mathlib.SolveByElim
import Mathport.Syntax.Translate.Tactic.Mathlib.Squeeze
import Mathport.Syntax.Translate.Tactic.Mathlib.Suggest
