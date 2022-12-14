/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Syntax.Translate.Basic

namespace Mathport.Translate

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param Command
open Lean.Elab (Visibility)
open Lean.Elab.Command (CommandElabM liftCoreM)
open AST3

partial def trTacticOrList : Spanned Tactic → M (Syntax.Tactic ⊕ Array Syntax.Tactic)
  | ⟨_, Tactic.«[]» args⟩ => Sum.inr <$> args.mapM fun arg => trTactic arg
  | tac => Sum.inl <$> trTactic tac

def trSeqFocusList : List (Spanned Tactic) → M Syntax.Tactic
  | [] => `(tactic| skip)
  | tac::rest => do
    let tac ← trTacticRaw tac
    if tac.raw.getKind == blockTransform then
      match rest with
      | [] => pure (fillBlockTransform tac #[])
      | tac2::rest => do
        let res ← go rest (← trTactic tac2)
        pure ⟨tac.raw.modifyArgs (·.push res)⟩
    else
      go rest tac
where
  go : List (Spanned Tactic) → Syntax.Tactic → M Syntax.Tactic
  | [], lhs => pure lhs
  | tac::rest, lhs => do
    match ← trTacticOrList tac with
    | .inl tac => go rest <|← `(tactic| $lhs <;> $tac)
    | .inr tacs => go rest <|← `(tactic| $lhs <;> [$tacs,*])

partial def trTactic' : Tactic → M Syntax.Tactic
  | .block bl => do `(tactic| · ($(← trBlock bl):tacticSeq))
  | .by tac => do `(tactic| · $(← trTactic tac):tactic)
  | .«;» tacs => trSeqFocusList tacs.toList
  | .«<|>» tacs => do
    `(tactic| first $[| $(← tacs.mapM fun tac => trTactic tac):tactic]*)
  | .«[]» _tacs => warn! "unsupported (impossible)"
  | .exact_shortcut ⟨m, Expr.calc args⟩ => withSpanS m do
    if h : args.size > 0 then
      `(tactic| calc $(← trCalcArg args[0]) $(← args[1:].toArray.mapM trCalcArg)*)
    else
      warn! "unsupported (impossible)"
  | .exact_shortcut e => do `(tactic| exact $(← trExpr e))
  | .expr e =>
    match e.unparen with
    | ⟨_, Expr.«`[]» tacs⟩ => trIdTactic ⟨true, none, none, tacs⟩
    | e => do
      let rec head
      | .const _ _ #[x] | .const ⟨_, x⟩ _ _ | .ident x => some x
      | .paren e => head e.kind
      | .app e _ => head e.kind
      | _ => none
      let rec fallback := do
        match ← trExpr e with
        | `(do $[$els]*) => `(tactic| run_tac $[$els:doSeqItem]*)
        | stx => `(tactic| run_tac $stx:term)
      match head e.kind with
      | none =>
        -- warn! "unsupported non-interactive tactic {repr e}"
        fallback
      | some n =>
        match (← get).niTactics.find? n with
        | some f => try f e.kind catch e => warn! "in {n}: {← e.toMessageData.toString}"
        | none => warn! "unsupported non-interactive tactic {n}" | fallback
  | Tactic.interactive n args => do
    match (← get).tactics.find? n with
    | some f => try f args catch e => warn! "in {n} {repr args}: {← e.toMessageData.toString}"
    | none => warn! "unsupported tactic {repr n} {repr args}"
