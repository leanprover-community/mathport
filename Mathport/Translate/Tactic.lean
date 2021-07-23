/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Translate.Basic
import Mathport.Translate.Parser

-- open Lean (Syntax Name mkIdent mkNode mkAtom)
open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport
namespace Translate

open AST3 Parser

namespace Tactic

structure Context where
  args : Array (Spanned Param)

structure State where
  pos : Nat := 0

abbrev TacM := ReaderT Context $ StateT State M

def TacM.run (m : TacM α) (args : Array (Spanned Param)) : M α := do
  let (a, ⟨n⟩) ← (m ⟨args⟩).run {}
  unless args.size = n do throw! "unsupported: too many args"
  a

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

def trLoc (loc : Location) : M (Option Syntax) := do
  let loc : Option Syntax ← match loc with
    | Location.wildcard =>
      some $ mkNode ``Parser.Tactic.locationWildcard #[mkAtom "*"]
    | Location.targets #[] false => throw! "unsupported"
    | Location.targets #[] true => none
    | Location.targets hs goal =>
      some $ mkNode ``Parser.Tactic.locationHyp #[
        mkNullNode $ hs.map mkIdent,
        mkOptionalNode $ if goal then mkAtom "⊢" else none]
  loc.map fun stx => mkNode ``Parser.Tactic.location #[mkAtom "at", stx]

syntax "propagateTags " tactic : tactic
def trPropagateTags : TacM Syntax := do
  `(tactic| propagateTags $(← trBlock (← itactic)))

def trIntro : TacM Syntax := do
  match ← parse ident_ ? with
  | none => `(tactic| intro)
  | some h => `(tactic| intro $(mkIdent h))

def trIntros : TacM Syntax := do
  match ← parse ident_* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intro $[$(hs.map mkIdent)]*)

syntax "introv " ident* : tactic
def trIntrov : TacM Syntax := do `(tactic| introv $[$((← parse ident_*).map mkIdent)]*)

syntax renameArg := ident " => " ident
syntax "rename' " renameArg,* : tactic
def trRenameArg : Name × Name → M Syntax
  | (x, y) => mkNode ``renameArg #[mkIdent x, mkAtom "=>", mkIdent y]

def trRename : TacM Syntax := do
  let renames ← parse renameArgs
  `(tactic| rename' $[$(← (renames.mapM trRenameArg : M _))],*)

def trApply : TacM Syntax := do `(tactic| apply $(← trExpr (← parse pExpr)))

syntax "fapply " term : tactic
def trFApply : TacM Syntax := do `(tactic| fapply $(← trExpr (← parse pExpr)))

syntax "eapply " term : tactic
def trEApply : TacM Syntax := do `(tactic| eapply $(← trExpr (← parse pExpr)))

syntax "apply " term " with " term : tactic
def trApplyWith : TacM Syntax := do
  `(tactic| apply $(← trExpr (← parse pExpr)) with $(← trExpr (← expr!)))

syntax "mapply " term : tactic
def trMApply : TacM Syntax := do `(tactic| mapply $(← trExpr (← parse pExpr)))

def trApplyInstance : TacM Syntax := `(tactic| inferInstance)

def trRefine : TacM Syntax := do `(tactic| refine' $(← trExpr (← parse pExpr)))

def trAssumption : TacM Syntax := do `(tactic| assumption)

macro "assumption'" : tactic => `(allGoals assumption)
def trAssumption' : TacM Syntax := do `(tactic| assumption')

def trChange : TacM Syntax := do
  let q ← trExpr (← parse pExpr)
  let h ← parse (tk "with" *> pExpr)?
  let loc ← trLoc (← parse location)
  match h with
  | none => `(tactic| change $q $[$loc]?)
  | some h => `(tactic| change $q with $(← trExpr h) $[$loc]?)
def trExact : TacM Syntax := do `(tactic| exact $(← trExpr (← parse pExpr)))

syntax "exacts" "[" term,* "]" : tactic
def trExacts : TacM Syntax := do
  `(tactic| exacts [$[$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr)],*])

def trRevert : TacM Syntax := do `(tactic| revert $[$((← parse ident_*).map mkIdent)]*)

syntax "toExpr' " term : tactic
def trToExpr' : TacM Syntax := do `(tactic| toExpr' $(← trExpr (← parse pExpr)))

def trRwRule (r : RwRule) : M Syntax := do
  mkNode ``Parser.Tactic.rwRule #[
    mkOptionalNode $ if r.symm then some (mkAtom "←") else none,
    ← trExpr r.rule]

def trRwArgs : TacM (Array Syntax × Option Syntax) := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  let loc ← trLoc (← parse location)
  if let some cfg ← expr? then
    dbg_trace "unsupported: rw with cfg"
  (q, loc)

def trRw : TacM Syntax := do let (q, loc) ← trRwArgs; `(tactic| rw [$[$q],*] $[$loc]?)

syntax (name := _root_.Lean.Parser.Tactic.rwSeq)
  "rwa " Parser.Tactic.rwRuleSeq (Parser.Tactic.location)? : tactic

def trRwA : TacM Syntax := do let (q, loc) ← trRwArgs; `(tactic| rwa [$[$q],*] $[$loc]?)

def trERw : TacM Syntax := do let (q, loc) ← trRwArgs; `(tactic| erw [$[$q],*] $[$loc]?)

def builtinTactics : List (Name × TacM Syntax) := [
  (`propagate_tags,      trPropagateTags),
  (`intro,               trIntro),
  (`intros,              trIntros),
  (`introv,              trIntrov),
  (`rename,              trRename),
  (`apply,               trApply),
  (`fapply,              trFApply),
  (`eapply,              trEApply),
  (`apply_with,          trApplyWith),
  (`mapply,              trMApply),
  (`apply_instance,      trApplyInstance),
  (`refine,              trRefine),
  (`assumption,          trAssumption),
  (`assumption',         trAssumption'),
  (`change,              trChange),
  (`exact,               trExact),
  (`from,                trExact),
  (`revert,              trRevert),
  (`to_expr',            trToExpr'),
  (`rewrite,             trRw),
  (`rw,                  trRw),
  (`rwa,                 trRwA),
  (`erewrite,            trERw),
  (`erw,                 trERw),
  (`with_cases,          throw "unsupported: with_cases"),
  (`generalize,          throw "supported: generalize"),
  (`induction,           throw "supported: induction"),
  (`case,                throw "supported: case"),
  (`destruct,            throw "unsupported: destruct"),
  (`cases,               throw "supported: cases"),
  (`cases_matching,      throw "unsupported: cases_matching"),
  (`casesm,              throw "unsupported: casesm"),
  (`cases_type,          throw "unsupported: cases_type"),
  (`trivial,             throw "supported: trivial"),
  (`admit,               throw "supported: admit"),
  (`sorry,               throw "unsupported: sorry"),
  (`contradiction,       throw "supported: contradiction"),
  (`iterate,             throw "unsupported: iterate"),
  (`repeat,              throw "supported: repeat"),
  (`try,                 throw "supported: try"),
  (`skip,                throw "supported: skip"),
  (`solve1,              throw "unsupported: solve1"),
  (`abstract,            throw "unsupported: abstract"),
  (`all_goals,           throw "supported: all_goals"),
  (`any_goals,           throw "unsupported: any_goals"),
  (`focus,               throw "supported: focus"),
  (`assume_core,         throw "unsupported: assume_core"),
  (`assume,              throw "unsupported: assume"),
  (`have,                throw "supported: have"),
  (`let,                 throw "supported: let"),
  (`suffices,            throw "supported: suffices"),
  (`trace_state,         throw "supported: trace_state"),
  (`trace,               throw "unsupported: trace"),
  (`existsi,             throw "supported: existsi"),
  (`constructor,         throw "supported: constructor"),
  (`econstructor,        throw "unsupported: econstructor"),
  (`left,                throw "unsupported: left"),
  (`right,               throw "unsupported: right"),
  (`split,               throw "unsupported: split"),
  (`contructor_matching, throw "unsupported: contructor_matching"),
  (`exfalso,             throw "unsupported: exfalso"),
  (`injection,           throw "supported: injection"),
  (`injections,          throw "unsupported: injections"),
  (`simp,                throw "supported: simp"),
  (`trace_simp_set,      throw "unsupported: trace_simp_set"),
  (`simp_intros,         throw "unsupported: simp_intros"),
  (`dsimp,               throw "unsupported: dsimp"),
  (`reflexivity,         throw "supported: reflexivity"),
  (`refl,                throw "supported: refl"),
  (`symmetry,            throw "unsupported: symmetry"),
  (`transitivity,        throw "unsupported: transitivity"),
  (`ac_reflexivity,      throw "unsupported: ac_reflexivity"),
  (`ac_refl,             throw "unsupported: ac_refl"),
  (`cc,                  throw "unsupported: cc"),
  (`subst,               throw "supported: subst"),
  (`subst_vars,          throw "unsupported: subst_vars"),
  (`clear,               throw "supported: clear"),
  (`dunfold,             throw "unsupported: dunfold"),
  (`delta,               throw "unsupported: delta"),
  (`unfold_projs,        throw "unsupported: unfold_projs"),
  (`unfold,              throw "unsupported: unfold"),
  (`unfold1,             throw "unsupported: unfold1"),
  (`apply_opt_param,     throw "unsupported: apply_opt_param"),
  (`apply_auto_param,    throw "unsupported: apply_auto_param"),
  (`fail_if_success,     throw "supported: fail_if_success"),
  (`success_if_fail,     throw "unsupported: success_if_fail"),
  (`guard_expr_eq,       throw "unsupported: guard_expr_eq"),
  (`guard_target,        throw "unsupported: guard_target"),
  (`guard_hyp,           throw "unsupported: guard_hyp"),
  (`match_target,        throw "unsupported: match_target"),
  (`by_cases,            throw "unsupported: by_cases"),
  (`funext,              throw "unsupported: funext"),
  (`by_contradiction,    throw "unsupported: by_contradiction"),
  (`by_contra,           throw "unsupported: by_contra"),
  (`type_check,          throw "unsupported: type_check"),
  (`done,                throw "supported: done"),
  (`show,                throw "supported: show"),
  (`specialize,          throw "unsupported: specialize"),
  (`congr,               throw "unsupported:congr ")
]