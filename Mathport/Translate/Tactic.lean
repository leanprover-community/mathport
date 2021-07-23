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

syntax "propagateTags " tacticSeq : tactic
def trPropagateTags : TacM Syntax := do
  `(tactic| propagateTags $(← trBlock (← itactic)):tacticSeq)

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

syntax "withCases " tacticSeq : tactic
def trWithCases : TacM Syntax := do `(tactic| withCases $(← trBlock (← itactic)):tacticSeq)

def trGeneralize : TacM Syntax := do
  let h ← parse ident ?
  parse (tk ":")
  let (e, x) ← parse generalizeArg
  `(tactic| generalize $[$(h.map mkIdent) :]? $(← trExpr e) = $(mkIdent x))

syntax (name := induction') "induction' " Parser.Tactic.casesTarget,+ (" using " ident)?
  (" with " ident+)? (" generalizing " ident+)? : tactic

def trInduction : TacM Syntax := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let rec_name := (← parse usingIdent).map mkIdent
  let ids ← parse withIdentList
  let revert := match (← parse (tk "generalizing" *> ident*)?).getD #[] with
  | #[] => none
  | ids => some (ids.map mkIdent)
  match hp, ids with
  | none, #[] => `(tactic| induction $e $[using $rec_name]? $[generalizing $[$revert]*]?)
  | _, _ =>
    `(tactic| induction' $[$(hp.map mkIdent) :]? $e $[using $rec_name]?
        with $[$(ids.map mkIdent)]* $[generalizing $[$revert]*]?)

def mkIdent_ : Name → Syntax
  | `_ => mkAtom "_"
  | x => mkIdent x

syntax caseArg := ident,+ " : " (ident <|> "_")*
syntax (name := case') "case' " (("[" caseArg,* "]") <|> caseArg) " => " tacticSeq : tactic
def trCase : TacM Syntax := do
  let args ← parse case
  let tac ← trBlock (← itactic)
  let trCaseArg
  | (tags, xs) => mkNode ``caseArg #[
    (mkAtom ",").mkSep (tags.map mkIdent), mkAtom ":", mkNullNode $ xs.map mkIdent_]
  match args with
  | #[(#[tag], xs)] => `(tactic| case $(mkIdent tag) $[$(xs.map mkIdent_)]* => $tac:tacticSeq)
  | #[arg] => `(tactic| case' $(trCaseArg arg):caseArg => $tac:tacticSeq)
  | _ => `(tactic| case' [$[$(args.map trCaseArg)],*] => $tac:tacticSeq)

syntax "destruct " term : tactic
def trDestruct : TacM Syntax := do `(tactic| destruct $(← trExpr (← parse pExpr)))

syntax (name := cases') "cases' " Parser.Tactic.casesTarget,+ (" using " ident)?
  (" with " ident+)? : tactic
def trCases : TacM Syntax := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let ids ← parse withIdentList
  match ids with
  | #[] => `(tactic| cases $[$(hp.map mkIdent) :]? $e)
  | _ => `(tactic| cases' $[$(hp.map mkIdent) :]? $e with $[$(ids.map mkIdent)]*)

syntax (name := casesM) "casesM" "*"? ppSpace term,* : tactic
def trCasesM : TacM Syntax := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| casesM $[$ps],*)
  | some () => `(tactic| casesM* $[$ps],*)

syntax (name := casesType) "casesType" "!"? "*"? ppSpace ident* : tactic
def trCasesType : TacM Syntax := do
  mkNode ``casesType #[
    mkAtom "casesType",
    mkOptionalNode $ (← parse (tk "!")?).map fun () => mkAtom "!",
    mkOptionalNode $ (← parse (tk "*")?).map fun () => mkAtom "*",
    mkNullNode $ (← parse ident*).map mkIdent]

def trTrivial : TacM Syntax := `(tactic| trivial)

syntax (name := «sorry») "sorry" : tactic
def trSorry : TacM Syntax := `(tactic| sorry)

def trContradiction : TacM Syntax := `(tactic| contradiction)

syntax (name := iterate) "iterate " (num)? tacticSeq : tactic
def trIterate : TacM Syntax := do
  match ← parse (smallNat)?, ← trBlock (← itactic) with
  | none, tac => `(tactic| repeat $tac:tacticSeq)
  | some n, tac => `(tactic| iterate $(Syntax.mkNumLit (toString n)) $tac:tacticSeq)

syntax (name := repeat') "repeat' " tacticSeq : tactic
def trRepeat : TacM Syntax := do `(tactic| repeat' $(← trBlock (← itactic)):tacticSeq)

def trTry : TacM Syntax := do `(tactic| try $(← trBlock (← itactic)):tacticSeq)

def trSkip : TacM Syntax := `(tactic| skip)

def trSolve1 : TacM Syntax := do trBlock (← itactic) TacticContext.one

syntax (name := abstract) "abstract " (ident)? tacticSeq : tactic
def trAbstract : TacM Syntax := do
  `(tactic| abstract $[$((← parse (ident)?).map mkIdent)]? $(← trBlock (← itactic)):tacticSeq)

def trAllGoals : TacM Syntax := do `(tactic| allGoals $(← trBlock (← itactic)):tacticSeq)

syntax (name := anyGoals) "anyGoals " tacticSeq : tactic
def trAnyGoals : TacM Syntax := do `(tactic| anyGoals $(← trBlock (← itactic)):tacticSeq)

def trFocus : TacM Syntax := do `(tactic| focus $(← trBlock (← itactic)):tacticSeq)

def trAssume : TacM Syntax := do
  match ← parse (Sum.inl <$> (tk ":" *> pExpr) <|> Sum.inr <$> parseBinders) with
  | Sum.inl ty => `(tactic| intro ($(mkIdent `this) : $(← trExpr ty)))
  | Sum.inr bis => `(tactic| intro $[$(← trIntroBinders bis)]*)
where
  trIntroBinder : Binder → Array Syntax → M (Array Syntax)
  | Binder.binder _ none _ _ _, out => do out.push $ ← `(_)
  | Binder.binder _ (some vars) _ none _, out => pure $
    vars.foldl (fun out v => out.push $ trBinderName v.kind) out
  | Binder.binder _ (some vars) bis (some ty) _, out => do
    let ty ← trDArrow bis ty.kind
    vars.foldlM (init := out) fun out v => do
      out.push $ ← `(($(trBinderName v.kind) : $ty))
  | Binder.collection _ _ _ _, out => throw! "unsupported: assume with binder collection"
  | Binder.notation _, out => throw! "unsupported: assume notation"

  trIntroBinders (bis : Array (Spanned Binder)) : M (Array Syntax) := do
    bis.foldlM (fun out bi => trIntroBinder bi.kind out) #[]

syntax (name := have'') "have " Parser.Term.haveIdLhs : tactic
def trHave : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let haveId := mkNode ``Parser.Term.haveIdDecl #[h, ty, mkAtom ":=", ← trExpr pr]
    `(tactic| have $haveId:haveDecl)
  | none => mkNode ``have'' #[mkAtom "have", h, ty]

syntax (name := let'') "let " Parser.Term.haveIdLhs : tactic
def trLet : TacM Syntax := do
  let h ← parse (ident)?
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let letId := mkNode ``Parser.Term.letIdDecl #[
      mkIdent (h.getD `this), ty, mkAtom ":=", ← trExpr pr]
    `(tactic| let $letId:letDecl)
  | none =>
    let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
    mkNode ``let'' #[mkAtom "let", h, ty]

syntax (name := suffices') "suffices " Parser.Term.haveIdLhs : tactic
def trSuffices : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  mkNode ``suffices' #[mkAtom "suffices", h, ty]

def trTraceState : TacM Syntax := `(tactic| traceState)

syntax (name := trace) "trace " term : tactic
def trTrace : TacM Syntax := do `(tactic| trace $(← trExpr (← expr!)))

syntax (name := existsi) "exists " term,* : tactic
def trExistsI : TacM Syntax := do
  `(tactic| exists $[$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr)],*)

def trConstructor : TacM Syntax := `(tactic| constructor)

syntax (name := eConstructor) "econstructor" : tactic
def trEConstructor : TacM Syntax := `(tactic| econstructor)

syntax (name := left) "left" : tactic
def trLeft : TacM Syntax := `(tactic| left)

syntax (name := right) "right" : tactic
def trRight : TacM Syntax := `(tactic| right)

syntax (name := split) "split" : tactic
def trSplit : TacM Syntax := `(tactic| split)

syntax (name := constructorM) "constructorM" "*"? ppSpace term,* : tactic
def trConstructorM : TacM Syntax := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| constructorM $[$ps],*)
  | some () => `(tactic| constructorM* $[$ps],*)

syntax (name := exFalso) "exFalso" : tactic
def trExFalso : TacM Syntax := `(tactic| exFalso)

def trInjection : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let hs := match ← parse withIdentList with
  | #[] => none
  | hs => some $ hs.map mkIdent_
  `(tactic| injection $e $[with $[$hs]*]?)

syntax (name := injections) "injections " (" with " (colGt (ident <|> "_"))+)? : tactic
def trInjections : TacM Syntax := do
  let hs := match ← parse withIdentList with
  | #[] => none
  | hs => some $ hs.map mkIdent_
  `(tactic| injections $[with $[$hs]*]?)

def trSimp : TacM Syntax := do
  let iota ← parse (tk "!")?
  if iota.isSome then dbg_trace "unsupported simp config option: iota_eqn"
  let trace ← parse (tk "?")?
  if trace.isSome then dbg_trace "unsupported simp config option: trace_lemmas"
  let only ← parse onlyFlag
  let hs ← parse simpArgList
  let (hs, all) ← hs.foldlM (init := (#[], true)) fun
  | (hs, all), SimpArg.allHyps => (hs, true)
  | (hs, all), SimpArg.symmExpr e => dbg_trace "unsupported: simp [← e]"; (hs, all)
  | (hs, all), SimpArg.expr e => do
    (hs.push $ mkNode ``Parser.Tactic.simpLemma #[mkNullNode, ← trExpr e], all)
  | (hs, all), SimpArg.except e => do
    (hs.push $ mkNode ``Parser.Tactic.simpErase #[mkAtom "-", mkIdent e], all)
  let attrs ← parse withIdentList
  unless attrs.isEmpty do dbg_trace "unsupported: simp sets"
  let loc ← parse location
  let cfg : Option Syntax := match ← expr? with
  | none => none
  | some (AST3.Expr.«{}») => none
  | some (AST3.Expr.structInst _ none flds #[] false) => do
    let mut cfg : Meta.Simp.Config := {}
    for (⟨_, _, n⟩, ⟨_, _, e⟩) in flds do
      match n, e with
      | `max_steps, Expr.nat n => cfg := {cfg with maxSteps := n}
      | `contextual, e => cfg := asBool e cfg fun cfg b => {cfg with contextual := b}
      | `zeta, e => cfg := asBool e cfg fun cfg b => {cfg with zeta := b}
      | `beta, e => cfg := asBool e cfg fun cfg b => {cfg with beta := b}
      | `eta, e => cfg := asBool e cfg fun cfg b => {cfg with eta := b}
      | `iota, e => cfg := asBool e cfg fun cfg b => {cfg with iota := b}
      | `proj, e => cfg := asBool e cfg fun cfg b => {cfg with proj := b}
      | `single_pass, e => cfg := asBool e cfg fun cfg b => {cfg with singlePass := b}
      | `memoize, e => cfg := asBool e cfg fun cfg b => {cfg with memoize := b}
      | _, _ => dbg_trace "unsupported simp config option: {n}"
    if cfg == {} then return none
    let default : Meta.Simp.Config := {}
    let a := #[]
      |> pushNat cfg {} `maxSteps (·.maxSteps)
      |> pushNat cfg {} `maxDischargeDepth (·.maxDischargeDepth)
      |> pushBool cfg {} `contextual (·.contextual)
      |> pushBool cfg {} `memoize (·.memoize)
      |> pushBool cfg {} `singlePass (·.singlePass)
      |> pushBool cfg {} `zeta (·.zeta)
      |> pushBool cfg {} `beta (·.beta)
      |> pushBool cfg {} `eta (·.eta)
      |> pushBool cfg {} `iota (·.iota)
      |> pushBool cfg {} `proj (·.proj)
      |> pushBool cfg {} `decide (·.decide)
    `({ $[$(a.pop):structInstField ,]* $(a.back):structInstField })
  | some _ => dbg_trace "unsupported simp config syntax"; none
  let cfg := match cfg with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  let only := if only then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := match hs with
  | #[] => mkNullNode
  | _ => mkNullNode #[mkAtom "[", (mkAtom ",").mkSep hs]
  match all, loc with
  | true, Location.wildcard =>
    mkNode ``Parser.Tactic.simpAll #[mkAtom "simp_all", cfg, only, hs]
  | _, _ => do
    if all then dbg_trace "unsupported: simp [*]"
    mkNode ``Parser.Tactic.simp #[mkAtom "simp", cfg, only, hs, mkOptionalNode $ ← trLoc loc]
where
  asBool {α} : AST3.Expr → α → (α → Bool → α) → α
  | AST3.Expr.const _ ⟨_, _, `tt⟩ _, a, f => f a true
  | AST3.Expr.const _ ⟨_, _, `ff⟩ _, a, f => f a false
  | _, a, _ => a
  push {β} [BEq β] (g : β → Syntax)
    {α} (a b : α) (n : Name) (f : α → β) (args : Array Syntax) : Array Syntax := do
    if f a == f b then args else
      args.push do `(Parser.Term.structInstField| $(mkIdent n):ident := $(g (f a)))
  pushNat := @push _ _ (Syntax.mkNumLit ∘ toString)
  pushBool := @push _ _ fun | true => do `(true) | false => do `(false)

def trTraceSimpSet : TacM Syntax := do
  let only ← parse onlyFlag
  let hs ← parse simpArgList
  let attrs ← parse withIdentList
  throw! "unsupported: trace_simp_set"

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
  (`with_cases,          trWithCases),
  (`generalize,          trGeneralize),
  (`induction,           trInduction),
  (`case,                trCase),
  (`destruct,            trDestruct),
  (`cases,               trCases),
  (`cases_matching,      trCasesM),
  (`casesm,              trCasesM),
  (`cases_type,          trCasesType),
  (`trivial,             trTrivial),
  (`admit,               trSorry),
  (`sorry,               trSorry),
  (`contradiction,       trContradiction),
  (`iterate,             trIterate),
  (`repeat,              trRepeat),
  (`try,                 trTry),
  (`skip,                trSkip),
  (`solve1,              trSolve1),
  (`abstract,            trAbstract),
  (`all_goals,           trAllGoals),
  (`any_goals,           trAnyGoals),
  (`focus,               trFocus),
  (`assume,              trAssume),
  (`have,                trHave),
  (`let,                 trLet),
  (`suffices,            trSuffices),
  (`trace_state,         trTraceState),
  (`trace,               trTrace),
  (`existsi,             trExistsI),
  (`constructor,         trConstructor),
  (`econstructor,        trEConstructor),
  (`left,                trLeft),
  (`right,               trRight),
  (`split,               trSplit),
  (`contructor_matching, trConstructorM),
  (`exfalso,             trExFalso),
  (`injection,           trInjection),
  (`injections,          trInjections),
  (`simp,                trSimp),
  (`trace_simp_set,      trTraceSimpSet),
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
  (`congr,               throw "unsupported: congr")]
