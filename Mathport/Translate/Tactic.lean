/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap
import Mathport.Translate.Basic

open Std (HashMap)
open Lean Elab Tactic

namespace Mathport
namespace Translate

open AST3

namespace Tactic

def trRw : Array Param → M Syntax
  | #[Param.parse _ q, Param.parse _ loc] => throw! "rw {repr (q, loc)}"
  | #[Param.parse _ q, Param.parse _ loc, Param.expr cfg] => throw! "unsupported (impossible)"
  | args => throw! "unsupported (impossible)"

def builtinTactics : List (Name × (Array Param → M Syntax)) :=
  [(`rw, trRw)]