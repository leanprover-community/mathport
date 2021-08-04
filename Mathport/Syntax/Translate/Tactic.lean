/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.Parser

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

def trPropagateTags : TacM Syntax := do
  `(tactic| propagateTags $(← trBlock (← itactic)):tacticSeq)

def trIntro : TacM Syntax := do
  match ← parse ident_ ? with
  | none => `(tactic| intro)
  | some h => `(tactic| intro $(mkIdent h):ident)

def trIntros : TacM Syntax := do
  match ← parse ident_* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intro $[$(hs.map mkIdent)]*)

def trIntrov : TacM Syntax := do `(tactic| introv $[$((← parse ident_*).map mkIdent)]*)

def trRenameArg : Name × Name → M Syntax
  | (x, y) => mkNode ``renameArg #[mkIdent x, mkAtom "=>", mkIdent y]

def trRename : TacM Syntax := do
  let renames ← parse renameArgs
  `(tactic| rename' $[$(← (renames.mapM trRenameArg : M _))],*)

def trApply : TacM Syntax := do `(tactic| apply $(← trExpr (← parse pExpr)))

def trFApply : TacM Syntax := do `(tactic| fapply $(← trExpr (← parse pExpr)))

def trEApply : TacM Syntax := do `(tactic| eapply $(← trExpr (← parse pExpr)))

def trApplyWith : TacM Syntax := do
  `(tactic| apply $(← trExpr (← parse pExpr)) with $(← trExpr (← expr!)))

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

def trExacts : TacM Syntax := do
  `(tactic| exacts [$[$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr)],*])

def trRevert : TacM Syntax := do `(tactic| revert $[$((← parse ident_*).map mkIdent)]*)

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

def trRwA : TacM Syntax := do let (q, loc) ← trRwArgs; `(tactic| rwa [$[$q],*] $[$loc]?)

def trERw : TacM Syntax := do let (q, loc) ← trRwArgs; `(tactic| erw [$[$q],*] $[$loc]?)

def trWithCases : TacM Syntax := do `(tactic| withCases $(← trBlock (← itactic)):tacticSeq)

def trGeneralize : TacM Syntax := do
  let h ← parse ident ?
  parse (tk ":")
  let (e, x) ← parse generalizeArg
  `(tactic| generalize $[$(h.map mkIdent) :]? $(← trExpr e) = $(mkIdent x))

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

def trDestruct : TacM Syntax := do `(tactic| destruct $(← trExpr (← parse pExpr)))

def trCases : TacM Syntax := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let ids ← parse withIdentList
  match ids with
  | #[] => `(tactic| cases $[$(hp.map mkIdent) :]? $e)
  | _ => `(tactic| cases' $[$(hp.map mkIdent) :]? $e with $[$(ids.map mkIdent)]*)

def trCasesM : TacM Syntax := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| casesM $[$ps],*)
  | some () => `(tactic| casesM* $[$ps],*)

def trCasesType : TacM Syntax := do
  mkNode ``Parser.Tactic.casesType #[
    mkAtom "casesType",
    mkOptionalNode $ (← parse (tk "!")?).map fun () => mkAtom "!",
    mkOptionalNode $ (← parse (tk "*")?).map fun () => mkAtom "*",
    mkNullNode $ (← parse ident*).map mkIdent]

def trTrivial : TacM Syntax := `(tactic| trivial)

def trSorry : TacM Syntax := `(tactic| sorry)

def trContradiction : TacM Syntax := `(tactic| contradiction)

def trIterate : TacM Syntax := do
  match ← parse (smallNat)?, ← trBlock (← itactic) with
  | none, tac => `(tactic| repeat $tac:tacticSeq)
  | some n, tac => `(tactic| iterate $(Syntax.mkNumLit (toString n)) $tac:tacticSeq)

def trRepeat : TacM Syntax := do `(tactic| repeat' $(← trBlock (← itactic)):tacticSeq)

def trTry : TacM Syntax := do `(tactic| try $(← trBlock (← itactic)):tacticSeq)

def trSkip : TacM Syntax := `(tactic| skip)

def trSolve1 : TacM Syntax := do trBlock (← itactic) TacticContext.one

def trAbstract : TacM Syntax := do
  `(tactic| abstract $[$((← parse (ident)?).map mkIdent)]? $(← trBlock (← itactic)):tacticSeq)

def trAllGoals : TacM Syntax := do `(tactic| allGoals $(← trBlock (← itactic)):tacticSeq)

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

def trHave : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let haveId := mkNode ``Parser.Term.haveIdDecl #[h, ty, mkAtom ":=", ← trExpr pr]
    `(tactic| have $haveId:haveIdDecl)
  | none => mkNode ``Parser.Tactic.have'' #[mkAtom "have", h, ty]

def trLet : TacM Syntax := do
  let h ← parse (ident)?
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr =>
    let letId := mkNode ``Parser.Term.letIdDecl #[
      mkIdent (h.getD `this), ty, mkAtom ":=", ← trExpr pr]
    `(tactic| let $letId:letIdDecl)
  | none =>
    let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
    mkNode ``Parser.Tactic.let'' #[mkAtom "let", h, ty]

def trSuffices : TacM Syntax := do
  let h ← parse (ident)?
  let h := mkNullNode $ match h with | none => #[] | some h => #[mkIdent h, mkNullNode]
  let ty := mkOptionalNode $ ← trOptType (← parse (tk ":" *> pExpr)?)
  mkNode ``Parser.Tactic.suffices' #[mkAtom "suffices", h, ty]

def trTraceState : TacM Syntax := `(tactic| traceState)

def trTrace : TacM Syntax := do `(tactic| trace $(← trExpr (← expr!)))

def trExistsI : TacM Syntax := do
  `(tactic| exists $[$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr)],*)

def trConstructor : TacM Syntax := `(tactic| constructor)

def trEConstructor : TacM Syntax := `(tactic| econstructor)

def trLeft : TacM Syntax := `(tactic| left)

def trRight : TacM Syntax := `(tactic| right)

def trSplit : TacM Syntax := `(tactic| split)

def trConstructorM : TacM Syntax := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| constructorM $[$ps],*)
  | some () => `(tactic| constructorM* $[$ps],*)

def trExFalso : TacM Syntax := `(tactic| exFalso)

def trInjection : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let hs := match ← parse withIdentList with
  | #[] => none
  | hs => some $ hs.map mkIdent_
  `(tactic| injection $e $[with $[$hs]*]?)

def trInjections : TacM Syntax := do
  let hs := match ← parse withIdentList with
  | #[] => none
  | hs => some $ hs.map mkIdent_
  `(tactic| injections $[with $[$hs]*]?)

def parseSimpConfig : Option AST3.Expr → Option Meta.Simp.Config
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
    cfg
  | some _ => dbg_trace "unsupported simp config syntax"; none
where
  asBool {α} : AST3.Expr → α → (α → Bool → α) → α
  | AST3.Expr.const _ ⟨_, _, `tt⟩ _, a, f => f a true
  | AST3.Expr.const _ ⟨_, _, `ff⟩ _, a, f => f a false
  | _, a, _ => a

def quoteSimpConfig (cfg : Meta.Simp.Config) : Option Syntax := do
  if cfg == {} then return none
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
where
  push {β} [BEq β] (g : β → Syntax)
    {α} (a b : α) (n : Name) (f : α → β) (args : Array Syntax) : Array Syntax := do
    if f a == f b then args else
      args.push do `(Parser.Term.structInstField| $(mkIdent n):ident := $(g (f a)))
  pushNat := @push _ _ (Syntax.mkNumLit ∘ toString)
  pushBool := @push _ _ fun | true => do `(true) | false => do `(false)

def trSimpArgs (hs : Array Parser.SimpArg) : M (Array Syntax × Bool) :=
  hs.foldlM (init := (#[], false)) fun
  | (hs, all), SimpArg.allHyps => (hs, true)
  | (hs, all), SimpArg.symmExpr e => dbg_trace "unsupported: simp [← e]"; (hs, all)
  | (hs, all), SimpArg.expr e => do
    (hs.push $ mkNode ``Parser.Tactic.simpLemma #[mkNullNode, ← trExpr e], all)
  | (hs, all), SimpArg.except e => do
    (hs.push $ mkNode ``Parser.Tactic.simpErase #[mkAtom "-", mkIdent e], all)

def trSimp : TacM Syntax := do
  let iota ← parse (tk "!")?
  if iota.isSome then dbg_trace "unsupported simp config option: iota_eqn"
  let trace ← parse (tk "?")?
  if trace.isSome then dbg_trace "unsupported simp config option: trace_lemmas"
  let only ← parse onlyFlag
  let (hs, all) ← trSimpArgs (← parse simpArgList)
  let attrs ← parse withIdentList
  unless attrs.isEmpty do dbg_trace "unsupported: simp sets"
  let loc ← parse location
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  let only := if only then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := match hs with
  | #[] => mkNullNode
  | _ => mkNullNode #[mkAtom "[", (mkAtom ",").mkSep hs, mkAtom "]"]
  match all, loc with
  | true, Location.wildcard =>
    mkNode ``Parser.Tactic.simpAll #[mkAtom "simp_all", cfg, only, hs]
  | _, _ => do
    if all then dbg_trace "unsupported: simp [*]"
    mkNode ``Parser.Tactic.simp #[mkAtom "simp", cfg, only, hs, mkOptionalNode $ ← trLoc loc]

def trTraceSimpSet : TacM Syntax := do
  let only ← parse onlyFlag
  let hs ← parse simpArgList
  let attrs ← parse withIdentList
  throw! "unsupported: trace_simp_set"

def trSimpIntros : TacM Syntax := do
  let ids ← parse ident_*
  let only ← parse onlyFlag
  let (hs, all) ← trSimpArgs (← parse simpArgList)
  if all then dbg_trace "unsupported: simp_intro [*]"
  let attrs ← parse withIdentList
  unless attrs.isEmpty do dbg_trace "unsupported: simp sets"
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  let ids := mkNullNode $ ids.map mkIdent
  let only := if only then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := match hs with
  | #[] => mkNullNode
  | _ => mkNullNode #[mkAtom "[", (mkAtom ",").mkSep hs, mkAtom "]"]
  mkNode ``Parser.Tactic.simpIntro #[mkAtom "simpIntro", cfg, ids, only, hs]

def trDSimp : TacM Syntax := do
  let only ← parse onlyFlag
  let (hs, all) ← trSimpArgs (← parse simpArgList)
  if all then dbg_trace "unsupported: dsimp [*]"
  let attrs ← parse withIdentList
  unless attrs.isEmpty do dbg_trace "unsupported: simp sets"
  let loc ← parse location
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  let only := if only then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := match hs with
  | #[] => mkNullNode
  | _ => mkNullNode #[mkAtom "[", (mkAtom ",").mkSep hs, mkAtom "]"]
  mkNode ``Parser.Tactic.dSimp #[mkAtom "dsimp",
    cfg, only, hs, mkOptionalNode $ ← trLoc loc]

def trRefl : TacM Syntax := `(tactic| rfl)

def trSymmetry : TacM Syntax := `(tactic| symm)

def trTransitivity : TacM Syntax := do
  `(tactic| trans $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

def trACRefl : TacM Syntax := `(tactic| acRfl)

def trCC : TacM Syntax := `(tactic| cc)

def trSubst : TacM Syntax := do
  let n ← match (← parse pExpr).unparen with
  | AST3.Expr.ident n => n
  | _ => throw! "unsupported"
  `(tactic| subst $(mkIdent n):ident)

def trSubstVars : TacM Syntax := `(tactic| substVars)

def trClear : TacM Syntax := do
  match ← parse ident* with
  | #[] => `(tactic| skip)
  | ids => `(tactic| clear $[$(ids.map mkIdent)]*)

def trDUnfold : TacM Syntax := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  mkNode ``Parser.Tactic.dUnfold #[mkAtom "dunfold", cfg,
    mkNullNode $ cs.map mkIdent, mkOptionalNode $ ← trLoc loc]

def trDelta : TacM Syntax := do
  `(tactic| delta $[$((← parse ident*).map mkIdent)]* $[$(← trLoc (← parse location))]?)

def trUnfoldProjs : TacM Syntax := do
  let loc ← parse location
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  mkNode ``Parser.Tactic.unfoldProjs #[mkAtom "unfoldProjs", cfg, mkOptionalNode $ ← trLoc loc]

def trUnfold : TacM Syntax := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  mkNode ``Parser.Tactic.unfold #[mkAtom "unfold", cfg,
    mkNullNode $ cs.map mkIdent, mkOptionalNode $ ← trLoc loc]

def trUnfold1 : TacM Syntax := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg := match (parseSimpConfig (← expr?)).bind quoteSimpConfig with
  | none => mkNullNode
  | some stx => mkNullNode #[mkAtom "(", mkAtom "config", mkAtom ":=", stx, mkAtom ")"]
  mkNode ``Parser.Tactic.unfold1 #[mkAtom "unfold1", cfg,
    mkNullNode $ cs.map mkIdent, mkOptionalNode $ ← trLoc loc]

def trApplyOptParam : TacM Syntax := `(tactic| inferOptParam)

def trApplyAutoParam : TacM Syntax := `(tactic| inferAutoParam)

def trFailIfSuccess : TacM Syntax := do `(tactic| failIfSuccess $(← trBlock (← itactic)):tacticSeq)

def trGuardExprEq : TacM Syntax := do
  let t ← expr!
  let p ← parse (tk ":=" *> pExpr)
  `(tactic| guardExprEq $(← trExpr t) := $(← trExpr p))

def trGuardTarget : TacM Syntax := do `(tactic| guardTarget $(← trExpr (← parse pExpr)))

def trGuardHyp : TacM Syntax := do
  `(tactic| guardHyp $(mkIdent (← parse ident))
    $[: $(← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr)]?
    $[:= $(← liftM $ (← parse (tk ":=" *> pExpr)?).mapM trExpr)]?)

def trMatchTarget : TacM Syntax := do
  let t ← trExpr (← parse pExpr)
  let m ← expr?
  if m.isSome then dbg_trace "unsupported: match_target reducibility"
  `(tactic| matchTarget $t)

def trByCases : TacM Syntax := do
  let (n, q) ← parse casesArg
  let q ← trExpr q
  `(tactic| byCases $[$(n.map mkIdent) :]? $q)

def trFunext : TacM Syntax := do `(tactic| funext $[$((← parse ident_*).map mkIdent_)]*)

def trByContra : TacM Syntax := do `(tactic| byContra $[$((← parse (ident)?).map mkIdent)]?)

def trTypeCheck : TacM Syntax := do `(tactic| typeCheck $(← trExpr (← parse pExpr)))

def trDone : TacM Syntax := do `(tactic| done)

def trShow : TacM Syntax := do `(tactic| show $(← trExpr (← parse pExpr)))

def trSpecialize : TacM Syntax := do
  let (head, args) ← trAppArgs (← parse pExpr) fun e =>
    match e.unparen with
    | Expr.ident h => h
    | _ => throw! "unsupported: specialize non-hyp"
  `(tactic| specialize $(mkIdent head) $[$args]*)

def trCongr : TacM Syntax := do `(tactic| congr)

mutual

partial def trRCasesPat : RCasesPat → M Syntax
  | RCasesPat.one `_ => `(rcasesPat| _)
  | RCasesPat.one x => `(rcasesPat| $(mkIdent x):ident)
  | RCasesPat.clear => do `(rcasesPat| -)
  | RCasesPat.tuple pats => do `(rcasesPat| ⟨$(← pats.mapM trRCasesPatLo),*⟩)
  | RCasesPat.alts #[pat] => trRCasesPat pat
  | pat => do `(rcasesPat| ($(← trRCasesPatLo pat)))

partial def trRCasesPatMed (pat : RCasesPat) : M Syntax := do
  let (fst, rest) ← match pat with
  | RCasesPat.alts pats =>
      (pats[0], ← pats[1:].toArray.mapM fun pat => do
        mkNullNode #[mkAtom "|", ← trRCasesPat pat])
  | pat => (pat, #[])
  mkNode ``Parser.Tactic.rcasesPatMed #[← trRCasesPat fst, mkNullNode rest]

partial def trRCasesPatLo (pat : RCasesPat) : M Syntax := do
  let (pat, ty) ← match pat with
  | RCasesPat.typed pat ty => (pat, mkNullNode #[mkAtom ":", ← trExpr ty])
  | _ => (pat, mkNullNode)
  Syntax.node ``Parser.Tactic.rcasesPatLo #[← trRCasesPatMed pat, ty]

end

def trRCases : TacM Syntax := do
  match ← parse rcasesArgs with
  | RCasesArgs.hint es depth => do
    let es := match es with | Sum.inl e => #[e] | Sum.inr es => es
    `(tactic| rcases? $[$(← liftM $ es.mapM trExpr):term],*
      $[: $(depth.map fun n => Syntax.mkNumLit (toString n))]?)
  | RCasesArgs.rcases n e pat => do
    `(tactic| rcases $[$(n.map mkIdent):ident :]? $(← trExpr e):term
              with $(← trRCasesPat pat):rcasesPat)
  | RCasesArgs.rcasesMany es pat => liftM $ show M _ from do
    `(tactic| rcases $[$(← es.mapM trExpr):term],* with $(← trRCasesPat pat):rcasesPat)

def trObtain : TacM Syntax := do
  let ((pat, tp), vals) ← parse obtainArg
  liftM $ show M _ from do
    `(tactic| obtain $[$(← pat.mapM trRCasesPat)]? $[: $(← tp.mapM trExpr)]?
      $[:= $[$(← vals.mapM (·.mapM trExpr))],*]?)

partial def trRIntroPat : RIntroPat → M Syntax
  | RIntroPat.one pat => do `(rintroPat| $(← trRCasesPat pat):rcasesPat)
  | RIntroPat.binder pats ty => do
    `(rintroPat| ($[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?))
  | RIntroPat.pat pat ty => do
    mkNode ``Parser.Tactic.rintroPat.binder #[mkAtom "(", ← trRCasesPatMed pat,
      mkNullNode (← match ty with | none => #[] | some ty => do #[mkAtom ":", ← trExpr ty]),
      mkAtom ")"]

def trRIntro : TacM Syntax := do
  liftM $ match ← parse rintroArg with
  | Sum.inr depth => `(tactic| rintro? $[: $(depth.map fun n => Syntax.mkNumLit (toString n))]?)
  | Sum.inl (pats, ty) => show M _ from do
    `(tactic| rintro $[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?)

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
  (`simp_intros,         trSimpIntros),
  (`dsimp,               trDSimp),
  (`reflexivity,         trRefl),
  (`refl,                trRefl),
  (`symmetry,            trSymmetry),
  (`transitivity,        trTransitivity),
  (`ac_reflexivity,      trACRefl),
  (`ac_refl,             trACRefl),
  (`cc,                  trCC),
  (`subst,               trSubst),
  (`subst_vars,          trSubstVars),
  (`clear,               trClear),
  (`dunfold,             trDUnfold),
  (`delta,               trDelta),
  (`unfold_projs,        trUnfoldProjs),
  (`unfold,              trUnfold),
  (`unfold1,             trUnfold1),
  (`apply_opt_param,     trApplyOptParam),
  (`apply_auto_param,    trApplyAutoParam),
  (`fail_if_success,     trFailIfSuccess),
  (`success_if_fail,     trFailIfSuccess),
  (`guard_expr_eq,       trGuardExprEq),
  (`guard_target,        trGuardTarget),
  (`guard_hyp,           trGuardHyp),
  (`match_target,        trMatchTarget),
  (`by_cases,            trByCases),
  (`funext,              trFunext),
  (`by_contradiction,    trByContra),
  (`by_contra,           trByContra),
  (`type_check,          trTypeCheck),
  (`done,                trDone),
  (`show,                trShow),
  (`specialize,          trSpecialize),
  (`congr,               trCongr),
  (`rcases,              trRCases),
  (`rintro,              trRIntro),
  (`rintros,             trRIntro),
  (`obtain,              trObtain)]
