/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic
import Lean

namespace Mathport
namespace Transform
open Lean Elab

def transformConsecutiveTactics : Syntax → Syntax → M Syntax
  | `(tactic| suffices : $ty:term), `(tactic|· $seq:tacticSeq) =>
    `(tactic| suffices $ty:term by $seq:tacticSeq)
  | `(tactic| have $[$id:ident]? $[: $ty:term]?), `(tactic|· $seq:tacticSeq) =>
    `(tactic| have $[$id:ident]? $[: $ty:term]? := by $seq:tacticSeq)
  | `(tactic| have $[$id:ident]? $[: $ty:term]?), `(tactic|exact $t) =>
    `(tactic| have $[$id:ident]? $[: $ty:term]? := $t)
  | `(tactic| let $id:ident $[: $ty:term]?), `(tactic|· $seq:tacticSeq) =>
    `(tactic| let $id:ident $[: $ty:term]? := by $seq:tacticSeq)
  | `(tactic| suffices : $ty:term), `(tactic|· $seq:tacticSeq) =>
    `(tactic| suffices $ty:term by $seq:tacticSeq)
  | `(tactic| obtain $[$pat]? $[: $ty]?), `(tactic|· $seq:tacticSeq) =>
    `(tactic| obtain $[$pat]? $[: $ty]? := by $seq:tacticSeq)
  | _, _ => throwUnsupported

mathport_rules
  | Syntax.node info ``Parser.Tactic.tacticSeq1Indented #[Syntax.node info2 `null tacs] => do
    for i in [1:tacs.size] do
      if let some tac' ← catchUnsupportedSyntax do
          transformConsecutiveTactics tacs[i-1][0] tacs[i][0] then
        let tacs' := tacs[0:i-1] ++ #[tacs[i].setArg 0 tac'] ++ tacs[i+1:tacs.size]
        return Syntax.node info ``Parser.Tactic.tacticSeq1Indented #[Syntax.node info2 `null tacs']
    throwUnsupported

-- common obsolete patterns from haveI
mathport_rules
  | `(by have $hd:haveDecl
         exact $t) =>
    `(have $hd:haveDecl
      $t)
  | `(by have $hd:haveDecl <;> exact $t) =>
    `(have $hd:haveDecl
      $t)

-- used in Lean 3 to postpone elaboration, now happens by default
mathport_rules | `(by exact $t) => t

mathport_rules
  | `(tactic| · · $seq:tacticSeq) => `(tactic| · $seq:tacticSeq)
  | `(conv| · · $seq:convSeq) => `(conv| · $seq:convSeq)

mathport_rules | `(by · $seq:tacticSeq) => `(by $seq:tacticSeq)

mathport_rules
  | `(Parser.Term.binderTactic| := by · $seq:tacticSeq) =>
    `(Parser.Term.binderTactic| := by $seq:tacticSeq)

mathport_rules
  | `(show $ty:term from by $seq:tacticSeq) =>
    `(show $ty:term by $seq:tacticSeq)
  | `(suffices $ty:term from by $seq:tacticSeq
      $t) =>
    `(suffices $ty:term by $seq:tacticSeq
      $t)
  | `(tactic| suffices $ty:term from by $seq:tacticSeq) =>
    `(tactic| suffices $ty:term by $seq:tacticSeq)

-- push `by` before `have`, `let`, `suffices` so that it can be formatted at the end of a line
mathport_rules
  | `(have $hd:haveDecl
      by $[$seq:tactic]*) =>
    `(by have $hd:haveDecl
        $[$seq:tactic]*)
  | `(let $ld:letDecl
      by $[$seq:tactic]*) =>
    `(by let $ld:letDecl
        $[$seq:tactic]*)
  | `(suffices $sd:sufficesDecl
      by $[$seq:tactic]*) =>
    `(by suffices $sd:sufficesDecl
        $[$seq:tactic]*)

-- expand `by (skip; skip)` to `by skip; skip`
mathport_rules
  | Syntax.node info ``Parser.Tactic.tacticSeq1Indented #[Syntax.node info2 `null tacs] => do
    let mut tacs' := #[]
    let mut modified := false
    for tac in tacs do
      match tac[0] with
      | `(tactic| ($seq:tacticSeq1Indented)) =>
        tacs' := tacs' ++ seq[0].getArgs
        modified := true
      | _ => tacs' := tacs'.push tac
    if modified then
      Syntax.node info ``Parser.Tactic.tacticSeq1Indented #[Syntax.node info2 `null tacs']
    else
      throwUnsupported
