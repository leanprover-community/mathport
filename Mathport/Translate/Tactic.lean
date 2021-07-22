/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Translate.Basic
import Mathport.Translate.Parser

open Lean (Syntax Name mkIdent mkNode mkAtom)

namespace Mathport
namespace Translate

open AST3 Parser

namespace Tactic

structure Context where
  args : Array (Spanned Param)

structure State where
  pos : Nat := 0

abbrev TacM := ReaderT Context $ StateT State M

def next? : TacM (Option Param) := do
  let args := (← read).args
  let i := (← get).pos
  if h : i < args.size then
    modify fun s => { s with pos := i+1 }
    (args.get ⟨i, h⟩).kind
  else none

def next! : TacM Param := do
  match ← next? with | some p => p | none => throw! "missing argument"

def parse (p : Parser.ParserM α) : TacM α := do
  let Param.parse _ args ← next! | throw! "expecting parse arg"
  match p ⟨(← readThe Translate.Context).commands, args⟩ |>.run' 0 with
  | none => throw! "parse error"
  | some a => a

def expr? : TacM (Option AST3.Expr) := do
  match ← next? with
  | none => none
  | some (Param.expr e) => some e.kind
  | _ => throw! "parse error"

def expr! : TacM AST3.Expr := do
  match ← expr? with | some p => p | none => throw! "missing argument"

def itactic : TacM AST3.Block := do
  let Param.block bl ← next! | throw! "expecting tactic arg"
  bl

syntax "propagateTags " tactic : tactic

def trPropagateTags : TacM Syntax := do
  `(tactic| propagateTags $(← trBlock (← itactic)))

def trIntro : TacM Syntax := do
  match ← parse (ident_)? with
  | none => `(tactic| intro)
  | some h => `(tactic| intro $(mkIdent h))

def trIntros : TacM Syntax := do
  match ← parse (ident_)* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intro $[$(hs.map mkIdent)]*)

def trIntrov : TacM Syntax := do
  let hs ← parse (ident_)*
  throw! "unsupported"

syntax renameArg := ident " => " ident
syntax "rename' " renameArg,* : tactic
def trRenameArg : Name × Name → M Syntax
  | (x, y) => mkNode ``renameArg #[mkIdent x, mkAtom "=>", mkIdent y]

def trRename : TacM Syntax := do
  let renames ← parse renameArgs
  `(tactic| rename' $[$(← (renames.mapM trRenameArg : M _))],*)

def trRw : TacM Syntax := do
  let q ← parse rwRules
  let loc ← parse location
  let cfg ← expr?
  throw! "unsupported"

def builtinTactics : List (Name × TacM Syntax) := [
  (`propagate_tags, trPropagateTags),
  (`intro, trIntro),
  (`intros, trIntros),
  (`introv, trIntrov),
  (`rename, trRename),
  (`apply, throw "unsupported"),
  (`fapply, throw "unsupported"),
  (`eapply, throw "unsupported"),
  (`apply_with, throw "unsupported"),
  (`mapply, throw "unsupported"),
  (`apply_instance, throw "unsupported"),
  (`refine, throw "unsupported"),
  (`assumption, throw "unsupported"),
  (`assumption', throw "unsupported"),
  (`change, throw "unsupported"),
  (`exact, throw "unsupported"),
  (`from, throw "unsupported"),
  (`revert, throw "unsupported"),
  (`to_expr', throw "unsupported"),
  (`rewrite, trRw),
  (`rw, trRw),
  (`rwa, throw "unsupported"),
  (`erewrite, throw "unsupported"),
  (`erw, throw "unsupported"),
  (`with_cases, throw "unsupported"),
  (`generalize, throw "unsupported"),
  (`induction, throw "unsupported"),
  (`case, throw "unsupported"),
  (`destruct, throw "unsupported"),
  (`cases, throw "unsupported"),
  (`cases_matching, throw "unsupported"),
  (`casesm, throw "unsupported"),
  (`cases_type, throw "unsupported"),
  (`trivial, throw "unsupported"),
  (`admit, throw "unsupported"),
  (`sorry, throw "unsupported"),
  (`contradiction, throw "unsupported"),
  (`iterate, throw "unsupported"),
  (`repeat, throw "unsupported"),
  (`try, throw "unsupported"),
  (`skip, throw "unsupported"),
  (`solve1, throw "unsupported"),
  (`abstract, throw "unsupported"),
  (`all_goals, throw "unsupported"),
  (`any_goals, throw "unsupported"),
  (`focus, throw "unsupported"),
  (`assume_core, throw "unsupported"),
  (`assume, throw "unsupported"),
  (`have, throw "unsupported"),
  (`let, throw "unsupported"),
  (`suffices, throw "unsupported"),
  (`trace_state, throw "unsupported"),
  (`trace, throw "unsupported"),
  (`existsi, throw "unsupported"),
  (`constructor, throw "unsupported"),
  (`econstructor, throw "unsupported"),
  (`left, throw "unsupported"),
  (`right, throw "unsupported"),
  (`split, throw "unsupported"),
  (`contructor_matching, throw "unsupported"),
  (`exfalso, throw "unsupported"),
  (`injection, throw "unsupported"),
  (`injections, throw "unsupported"),
  (`simp, throw "unsupported"),
  (`trace_simp_set, throw "unsupported"),
  (`simp_intros, throw "unsupported"),
  (`dsimp, throw "unsupported"),
  (`reflexivity, throw "unsupported"),
  (`refl, throw "unsupported"),
  (`symmetry, throw "unsupported"),
  (`transitivity, throw "unsupported"),
  (`ac_reflexivity, throw "unsupported"),
  (`ac_refl, throw "unsupported"),
  (`cc, throw "unsupported"),
  (`subst, throw "unsupported"),
  (`subst_vars, throw "unsupported"),
  (`clear, throw "unsupported"),
  (`dunfold, throw "unsupported"),
  (`delta, throw "unsupported"),
  (`unfold_projs, throw "unsupported"),
  (`unfold, throw "unsupported"),
  (`unfold1, throw "unsupported"),
  (`apply_opt_param, throw "unsupported"),
  (`apply_auto_param, throw "unsupported"),
  (`fail_if_success, throw "unsupported"),
  (`success_if_fail, throw "unsupported"),
  (`guard_expr_eq, throw "unsupported"),
  (`guard_target, throw "unsupported"),
  (`guard_hyp, throw "unsupported"),
  (`match_target, throw "unsupported"),
  (`by_cases, throw "unsupported"),
  (`funext, throw "unsupported"),
  (`by_contradiction, throw "unsupported"),
  (`by_contra, throw "unsupported"),
  (`type_check, throw "unsupported"),
  (`done, throw "unsupported"),
  (`show, throw "unsupported"),
  (`specialize, throw "unsupported"),
  (`congr, throw "unsupported")
]