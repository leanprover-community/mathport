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

partial def trTacticOrList : Spanned Tactic → M (Sum Syntax.Tactic (Array Syntax.Tactic))
  | ⟨_, Tactic.«[]» args⟩ => Sum.inr <$> args.mapM fun arg => trTactic arg
  | tac => Sum.inl <$> trTactic tac

partial def trTactic' : Tactic → M Syntax.Tactic
  | Tactic.block bl => do `(tactic| · ($(← trBlock bl):tacticSeq))
  | Tactic.by tac => do `(tactic| · $(← trTactic tac):tactic)
  | Tactic.«;» tacs => do
    let rec build (i : Nat) (lhs : Syntax.Tactic) : M Syntax.Tactic :=
      if h : i < tacs.size then do
        match ← trTacticOrList tacs[i] with
        | Sum.inl tac => `(tactic| $lhs <;> $(← build (i+1) tac))
        | Sum.inr tacs => build (i+1) (← `(tactic| $lhs <;> [$tacs,*]))
      else pure lhs
    if h : tacs.size > 0 then
      build 1 (← trTactic tacs[0])
    else
      `(tactic| skip)
  | Tactic.«<|>» tacs => do
    `(tactic| first $[| $(← tacs.mapM fun tac => trTactic tac):tactic]*)
  | Tactic.«[]» _tacs => warn! "unsupported (impossible)"
  | Tactic.exact_shortcut ⟨m, Expr.calc args⟩ => withSpanS m do
    if h : args.size > 0 then
      `(tactic| calc $(← trCalcArg args[0]) $(← args[1:].toArray.mapM trCalcArg)*)
    else
      warn! "unsupported (impossible)"
  | Tactic.exact_shortcut e => do `(tactic| exact $(← trExpr e))
  | Tactic.expr e =>
    match e.unparen with
    | ⟨_, Expr.«`[]» tacs⟩ => trIdTactic ⟨true, none, none, tacs⟩
    | e => do
      let rec head
      | Expr.ident x => x
      | Expr.paren e => head e.kind
      | Expr.app e _ => head e.kind
      | _ => Name.anonymous
      match Rename.resolveIdent? (← getEnv) (head e.kind) with
      | none =>
        -- warn! "unsupported non-interactive tactic {repr e}"
        match ← trExpr e with
        | `(do $[$els]*) => `(tactic| run_tac $[$els:doSeqItem]*)
        | stx => `(tactic| run_tac $stx:term)
      | some n =>
        match (← get).niTactics.find? n with
        | some f => try f e.kind catch e => warn! "in {n}: {← e.toMessageData.toString}"
        | none => warn! "unsupported non-interactive tactic {n}"
  | Tactic.interactive n args => do
    match (← get).tactics.find? n with
    | some f => try f args catch e => warn! "in {n} {repr args}: {← e.toMessageData.toString}"
    | none => warn! "unsupported tactic {repr n} {repr args}"
