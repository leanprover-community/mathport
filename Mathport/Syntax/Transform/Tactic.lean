/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathport.Syntax.Transform.Basic
import Lean

namespace Mathport
namespace Transform
open Lean Elab Mathlib.Tactic

def trHaveArgs (id : TSyntax ``optBinderIdent) (bs : TSyntaxArray ``Parser.Term.letIdBinder)
    (ty : Option Term) (val : Term) : M (TSyntax ``Parser.Term.haveIdDecl) :=
  match id with
  | `(optBinderIdent| $id:ident) => `(Parser.Term.haveIdDecl| $id:ident $bs* $[: $ty]? := $val)
  | `(optBinderIdent| _%$id) => `(Parser.Term.haveIdDecl| _%$id $bs* $[: $ty]? := $val)
  | `(optBinderIdent| $id:hygieneInfo) =>
    `(Parser.Term.haveIdDecl| $id:hygieneInfo $bs* $[: $ty]? := $val)
  | _ => throwUnsupported

def transformConsecutiveTactics : Syntax.Tactic → Syntax.Tactic → M Syntax.Tactic
  | `(tactic| suffices : $ty), `(tactic|· $tacs*) =>
    `(tactic| suffices $ty by $tacs*)
  | `(tactic| have $id:optBinderIdent $bs* $[: $ty]?), `(tactic|· $tacs*) => do
    `(tactic| have $(← trHaveArgs id bs ty <|← `(by $tacs*)):haveIdDecl)
  | `(tactic| have $id:optBinderIdent $bs* $[: $ty]?), `(tactic|exact $t) => do
    `(tactic| have $(← trHaveArgs id bs ty t):haveIdDecl)
  | `(tactic| let $id:ident $bs* $[: $ty]?), `(tactic|· $tacs*) =>
    `(tactic| let $id:ident $bs* $[: $ty]? := by $tacs*)
  | `(tactic| let _%$id $bs* $[: $ty]?), `(tactic|· $tacs*) =>
    `(tactic| let _%$id $bs* $[: $ty]? := by $tacs*)
  | `(tactic| let $bs:letIdBinder* $[: $ty]?), `(tactic|· $tacs*) =>
    `(tactic| let this $bs* $[: $ty]? := by $tacs*)
  | `(tactic| obtain $(pat)? $[: $ty]?), `(tactic|· $tacs*) =>
    `(tactic| obtain $(pat)? $[: $ty]? := by $tacs*)
  | _, _ => throwUnsupported

def transformConsecutiveTacticsArray (tacAndSeps : Array Syntax) : M (Array Syntax) := do
  for i in [1:(tacAndSeps.size+1)/2] do
    if let some tac' ← catchUnsupportedSyntax do withRef tacAndSeps[2*(i-1)]! do
        transformConsecutiveTactics ⟨tacAndSeps[2*(i-1)]!⟩ ⟨tacAndSeps[2*i]!⟩  then
      return tacAndSeps[:2*(i-1)] ++ #[tac'] ++ tacAndSeps[2*i+1:]
  throwUnsupported

-- expand `by (skip; skip)` to `by skip; skip`
def transformInlineTactics (tacAndSeps : Array Syntax) : M (Array Syntax) := do
  let mut tacs' := #[]
  let mut modified := false
  for i in [:(tacAndSeps.size+1)/2] do
    let tac := tacAndSeps[2*i]!
    match tac with
    | `(tactic| ($seq:tacticSeq1Indented)) =>
      tacs' := tacs' ++ seq.1[0].getArgs
      modified := true
    | _ => tacs' := tacs'.push tac
    if let some sep := tacAndSeps[2*i+1]? then
      tacs' := tacs'.push sep
  unless modified do throwUnsupported
  pure tacs'

def transformInlineConvs (tacs : Array Syntax.Conv) : M (Array Syntax.Conv) := do
  let mut tacs' := #[]
  let mut modified := false
  for tac in tacs do
    match tac.1 with
    | `(conv| ($[$seq:conv]*)) =>
      tacs' := tacs' ++ seq
      modified := true
    | _ => tacs' := tacs'.push tac
  unless modified do throwUnsupported
  pure tacs'

def transformTacticsArray (tacAndSeps : Array Syntax) : M (Array Syntax) := do
  for fn in #[transformConsecutiveTacticsArray, transformInlineTactics] do
    if let some tacs' ← catchUnsupportedSyntax <| fn tacAndSeps then
      return tacs'
  throwUnsupported

open Parser.Tactic TSyntax.Compat in
mathport_rules
  | stx@`(tacticSeq1Indented| $[$_:tactic]*) => do
    (stx.setArg 0 ∘ stx[0].setArgs) <$> transformTacticsArray stx[0].getArgs
  | `(tactic| · $stx:tacticSeq1Indented) => do
    let args ← transformTacticsArray stx.1[0].getArgs
    `(tactic| · $(stx.1.setArg 0 <| stx.1[0].setArgs args):tacticSeq1Indented)
  | `(Conv.convSeq| $[$tac:conv]*) => do
    `(Conv.convSeq| $[$(← transformInlineConvs tac):conv]*)

-- common obsolete patterns from haveI
mathport_rules
  | `(by have $hd:haveDecl; exact $t) =>
    `(haveI $hd:haveDecl
      $t)
  | `(by have $hd:haveDecl <;> exact $t) =>
    `(haveI $hd:haveDecl
      $t)
  | `(by haveI $hd:haveDecl; exact $t) =>
    `(haveI $hd:haveDecl
      $t)
  | `(by haveI $hd:haveDecl <;> exact $t) =>
    `(haveI $hd:haveDecl
      $t)
  | `(by letI $hd:haveDecl; exact $t) =>
    `(letI $hd:haveDecl
      $t)
  | `(by letI $hd:haveDecl <;> exact $t) =>
    `(letI $hd:haveDecl
      $t)

-- used in Lean 3 to postpone elaboration, now happens by default
mathport_rules | `(by exact $t) => pure t

mathport_rules
  | `(tactic| · · $seq:tacticSeq) => `(tactic| · $seq:tacticSeq)
  | `(conv| · · $seq:convSeq) => `(conv| · $seq:convSeq)

mathport_rules | `(by · $seq:tactic*) => `(by $seq:tactic*)

mathport_rules
  | `(Parser.Term.binderTactic| := by · $seq:tactic*) =>
    `(Parser.Term.binderTactic| := by $seq:tactic*)

mathport_rules
  | `(show $ty:term from by $seq:tacticSeq) =>
    `(show $ty:term by $seq:tacticSeq)
  | `(suffices $ty:term from by $seq:tacticSeq; $t:term) =>
    `(suffices $ty:term by $seq:tacticSeq
      $t)
  | `(tactic| suffices $ty:term from by $seq:tacticSeq) =>
    `(tactic| suffices $ty:term by $seq:tacticSeq)

-- push `by` before `have`, `let`, `suffices` so that it can be formatted at the end of a line
mathport_rules
  | `(have $hd:haveDecl; by $seq:tactic*) =>
    `(by have $hd:haveDecl
         $[$seq:tactic]*)
  | `(let $ld:letDecl; by $seq:tactic*) =>
    `(by let $ld:letDecl
         $seq:tactic*)
  | `(suffices $sd:sufficesDecl; by $seq:tactic*) =>
    `(by suffices $sd:sufficesDecl
         $seq:tactic*)
