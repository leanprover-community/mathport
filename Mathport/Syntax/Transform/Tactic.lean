/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic

namespace Mathport
namespace Transform
open Lean Elab

def transformConsecutiveTactics : Syntax → Syntax → M Syntax
  | `(tactic| suffices : $ty:term), `(tactic|· $seq:tacticSeq) =>
    `(tactic| suffices $ty:term by $seq:tacticSeq)
  | `(tactic| have $id:ident : $ty:term), `(tactic|· $seq:tacticSeq) =>
    `(tactic| have $id:ident : $ty:term := by $seq:tacticSeq)
  | _, _ => throwUnsupported

mathport_rules
  | Syntax.node info ``Parser.Tactic.tacticSeq1Indented #[Syntax.node info2 `null tacs] => do
    for i in [1:tacs.size] do
      if let some tac' ← catchUnsupportedSyntax do
          transformConsecutiveTactics tacs[i-1][0] tacs[i][0] then
        let tacs' := tacs[0:i-1] ++ #[tacs[i].setArg 0 tac'] ++ tacs[i+1:tacs.size]
        dbg_trace tacs'
        return Syntax.node info ``Parser.Tactic.tacticSeq1Indented #[Syntax.node info2 `null tacs']
    throwUnsupported
