/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

def trLoc (loc : Location) : M (Option Syntax) := do
  let loc : Option Syntax ← match loc with
    | Location.wildcard =>
      pure $ some $ mkNode ``Parser.Tactic.locationWildcard #[mkAtom "*"]
    | Location.targets #[] false => warn! "unsupported"
    | Location.targets #[] true => pure none
    | Location.targets hs goal =>
      pure $ some $ mkNode ``Parser.Tactic.locationHyp #[
        mkNullNode hs,
        mkOptionalNode $ if goal then mkAtom "⊢" else none]
  pure $ loc.map fun stx => mkNode ``Parser.Tactic.location #[mkAtom "at", stx]

@[trTactic propagate_tags] def trPropagateTags : TacM Syntax := do
  `(tactic| propagate_tags $(← trBlock (← itactic)):tacticSeq)

@[trTactic intro] def trIntro : TacM Syntax := do
  match ← parse (ident_)? with
  | some (BinderName.ident h) => `(tactic| intro $(mkIdent h):ident)
  | _ => `(tactic| intro)

@[trTactic intros] def trIntros : TacM Syntax := do
  match ← parse ident_* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intro $[$(hs.map trBinderName)]*)

@[trTactic introv] def trIntrov : TacM Syntax := do
  `(tactic| introv $((← parse ident_*).map trBinderIdent)*)

@[trTactic rename] def trRename : TacM Syntax := do
  let renames ← parse renameArgs
  let as := renames.map fun (a, b) => mkIdent a
  let bs := renames.map fun (a, b) => mkIdent b
  `(tactic| rename' $[$as:ident => $bs],*)

@[trTactic apply] def trApply : TacM Syntax := do `(tactic| apply $(← trExpr (← parse pExpr)))

@[trTactic fapply] def trFApply : TacM Syntax := do `(tactic| fapply $(← trExpr (← parse pExpr)))

@[trTactic eapply] def trEApply : TacM Syntax := do `(tactic| eapply $(← trExpr (← parse pExpr)))

@[trTactic apply_with] def trApplyWith : TacM Syntax := do
  `(tactic| apply $(← trExpr (← parse pExpr)) with $(← trExpr (← expr!)))

@[trTactic mapply] def trMApply : TacM Syntax := do `(tactic| mapply $(← trExpr (← parse pExpr)))

@[trTactic apply_instance] def trApplyInstance : TacM Syntax := `(tactic| infer_instance)
@[trNITactic tactic.apply_instance] def trNIApplyInstance (_ : AST3.Expr) : M Syntax :=
  `(tactic| infer_instance)

@[trTactic refine] def trRefine : TacM Syntax := do `(tactic| refine' $(← trExpr (← parse pExpr)))

@[trTactic assumption] def trAssumption : TacM Syntax := do `(tactic| assumption)

@[trTactic assumption'] def trAssumption' : TacM Syntax := do `(tactic| assumption')

@[trTactic change] def trChange : TacM Syntax := do
  let q ← trExpr (← parse pExpr)
  let h ← parse (tk "with" *> pExpr)?
  let loc ← trLoc (← parse location)
  match h with
  | none => `(tactic| change $q $[$loc]?)
  | some h => `(tactic| change $q with $(← trExpr h) $[$loc]?)

@[trTactic exact «from»] def trExact : TacM Syntax := do
  `(tactic| exact $(← trExpr (← parse pExpr)))

@[trTactic exacts] def trExacts : TacM Syntax := do
  `(tactic| exacts [$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*])

@[trTactic revert] def trRevert : TacM Syntax := do
  `(tactic| revert $[$((← parse ident*).map mkIdent)]*)

def trRwRule (r : RwRule) : M Syntax :=
  return mkNode ``Parser.Tactic.rwRule #[
    mkOptionalNode $ if r.symm then some (mkAtom "←") else none,
    ← trExpr r.rule]

def trRwArgs : TacM (Array Syntax × Option Syntax) := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  let loc ← trLoc (← parse location)
  if let some cfg ← expr? then
    warn! "warning: unsupported: rw with cfg: {repr cfg}"
  pure (q, loc)

@[trTactic rewrite rw] def trRw : TacM Syntax := do
  let (q, loc) ← trRwArgs; `(tactic| rw [$q,*] $(loc)?)

@[trTactic rwa] def trRwA : TacM Syntax := do
  let (q, loc) ← trRwArgs; `(tactic| rwa [$q,*] $(loc)?)

@[trTactic erewrite erw] def trERw : TacM Syntax := do
  let (q, loc) ← trRwArgs; `(tactic| erw [$q,*] $(loc)?)

@[trTactic with_cases] def trWithCases : TacM Syntax := do
  `(tactic| with_cases $(← trBlock (← itactic)):tacticSeq)

@[trTactic generalize] def trGeneralize : TacM Syntax := do
  let h ← parse (ident)? <* parse (tk ":")
  let (e, x) ← parse generalizeArg
  `(tactic| generalize $[$(h.map mkIdent) :]? $(← trExpr e) = $(mkIdent x))

@[trTactic induction] def trInduction : TacM Syntax := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let rec_name ← liftM $ (← parse usingIdent).mapM mkIdentI
  let ids ← parse withIdentList
  let revert := (← parse (tk "generalizing" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  match hp, ids with
  | none, #[] => `(tactic| induction $e $[using $rec_name]? $[generalizing $[$revert]*]?)
  | _, _ =>
    `(tactic| induction' $[$(hp.map mkIdent) :]? $e $[using $rec_name]?
        with $(ids.map trBinderIdent)* $[generalizing $revert*]?)

@[trTactic case] def trCase : TacM Syntax := do
  let args ← parse case
  let tac ← trBlock (← itactic)
  let trCaseArg := fun (tags, xs) => do
    let tags ← tags.mapM (trBinderIdentI ·)
    `(Parser.Tactic.caseArg| $[$tags],* $[: $((xs.map trIdent_).asNonempty)*]?)
  match args with
  | #[(#[BinderName.ident tag], xs)] =>
    `(tactic| case $(mkIdent tag) $(xs.map trIdent_)* => $tac:tacticSeq)
  | #[arg] => `(tactic| case'' $(← trCaseArg arg):caseArg => $tac:tacticSeq)
  | _ => `(tactic| case'' [$(← args.mapM trCaseArg),*] => $tac:tacticSeq)

@[trTactic destruct] def trDestruct : TacM Syntax := do
  `(tactic| destruct $(← trExpr (← parse pExpr)))

@[trTactic cases] def trCases : TacM Syntax := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let ids ← parse withIdentList
  match ids with
  | #[] => `(tactic| cases $[$(hp.map mkIdent) :]? $e)
  | _ => `(tactic| cases' $[$(hp.map mkIdent) :]? $e with $(ids.map trBinderIdent)*)

@[trTactic cases_matching casesm] def trCasesM : TacM Syntax := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| casesm $ps,*)
  | some () => `(tactic| casesm* $ps,*)

@[trTactic cases_type] def trCasesType : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.casesType, "cases_type")
  | some _ => (``Parser.Tactic.casesType!, "cases_type!")
  pure $ mkNode tac #[mkAtom s,
    mkOptionalNode $ (← parse (tk "*")?).map fun () => mkAtom "*",
    mkNullNode $ (← parse ident*).map mkIdent]

@[trTactic trivial] def trTrivial : TacM Syntax := `(tactic| trivial)

@[trTactic admit «sorry»] def trSorry : TacM Syntax := `(tactic| sorry)

@[trTactic contradiction] def trContradiction : TacM Syntax := `(tactic| contradiction)

@[trTactic iterate] def trIterate : TacM Syntax := do
  match ← parse (smallNat)?, ← trBlock (← itactic) with
  | none, tac => `(tactic| repeat $tac:tacticSeq)
  | some n, tac => `(tactic| iterate $(Quote.quote n) $tac:tacticSeq)

@[trTactic «repeat»] def trRepeat : TacM Syntax := do
  `(tactic| repeat' $(← trBlock (← itactic)):tacticSeq)

@[trTactic «try»] def trTry : TacM Syntax := do `(tactic| try $(← trBlock (← itactic)):tacticSeq)

@[trTactic skip] def trSkip : TacM Syntax := `(tactic| skip)

@[trTactic solve1] def trSolve1 : TacM Syntax := do `(tactic| · ($(← trBlock (← itactic)):tacticSeq))

@[trTactic abstract] def trAbstract : TacM Syntax := do
  `(tactic| abstract $(← liftM $ (← parse (ident)?).mapM mkIdentF)?
      $(← trBlock (← itactic)):tacticSeq)

@[trTactic all_goals] def trAllGoals : TacM Syntax := do
  `(tactic| all_goals $(← trBlock (← itactic)):tacticSeq)

@[trTactic any_goals] def trAnyGoals : TacM Syntax := do
  `(tactic| any_goals $(← trBlock (← itactic)):tacticSeq)

@[trTactic focus] def trFocus : TacM Syntax := do
  `(tactic| focus $(← trBlock (← itactic)):tacticSeq)

@[trTactic assume] def trAssume : TacM Syntax := do
  match ← parse (Sum.inl <$> (tk ":" *> pExpr) <|> Sum.inr <$> parseBinders) with
  | Sum.inl ty => `(tactic| intro ($(mkIdent `this) : $(← trExpr ty)))
  | Sum.inr bis => `(tactic| intro $[$(← trIntroBinders bis)]*)
where
  trIntroBinder : Binder → Array Syntax → M (Array Syntax)
  | Binder.binder _ none _ _ _, out => out.push <$> `(_)
  | Binder.binder _ (some vars) _ none _, out => pure $
    vars.foldl (fun out v => out.push $ trBinderName v.kind) out
  | Binder.binder _ (some vars) bis (some ty) _, out => do
    let ty ← trDArrow bis ty
    vars.foldlM (init := out) fun out v =>
      out.push <$> `(($(trBinderName v.kind) : $ty))
  | Binder.collection _ _ _ _, out => warn! "unsupported: assume with binder collection"
  | Binder.notation _, out => warn! "unsupported: assume notation"

  trIntroBinders (bis : Array (Spanned Binder)) : M (Array Syntax) := do
    bis.foldlM (fun out bi => trIntroBinder bi.kind out) #[]

@[trTactic «have»] def trHave : TacM Syntax := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| have $[$h:ident]? $[: $ty:term]? := $(← trExpr pr))
  | none => `(tactic| have $[$h:ident]? $[: $ty:term]?)

@[trTactic «let»] def trLet : TacM Syntax := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => match h with
    | some h => `(tactic| let $h:ident $[: $ty:term]? := $(← trExpr pr))
    | none => `(tactic| let this $[: $ty:term]? := $(← trExpr pr))
  | none =>
    `(tactic| let $[$h:ident]? $[: $ty:term]?)

@[trTactic «suffices»] def trSuffices : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  `(tactic| suffices $[$h:ident]? $[: $ty:term]?)

@[trTactic trace_state] def trTraceState : TacM Syntax := `(tactic| trace_state)

@[trTactic trace] def trTrace : TacM Syntax := do `(tactic| trace $(← trExpr (← expr!)))

@[trTactic existsi] def trExistsI : TacM Syntax := do
  `(tactic| exists $(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*)

@[trTactic constructor] def trConstructor : TacM Syntax := `(tactic| constructor)

@[trTactic econstructor] def trEConstructor : TacM Syntax := `(tactic| econstructor)

@[trTactic left] def trLeft : TacM Syntax := `(tactic| left)

@[trTactic right] def trRight : TacM Syntax := `(tactic| right)

@[trTactic split] def trSplit : TacM Syntax := `(tactic| constructor)

@[trTactic constructor_matching] def trConstructorM : TacM Syntax := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| constructorm $ps,*)
  | some () => `(tactic| constructorm* $ps,*)

@[trTactic exfalso] def trExfalso : TacM Syntax := `(tactic| exfalso)

@[trTactic injection] def trInjection : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let hs := (← parse withIdentList).map trIdent_ |>.asNonempty
  `(tactic| injection $e $[with $hs*]?)

@[trTactic injections] def trInjections : TacM Syntax := do
  let hs := (← parse withIdentList).map trIdent_ |>.asNonempty
  `(tactic| injections $[with $hs*]?)

def parseSimpConfig : Option (Spanned AST3.Expr) → M (Option Meta.Simp.Config × Option Syntax)
  | none => pure (none, none)
  | some ⟨_, AST3.Expr.«{}»⟩ => pure (none, none)
  | some ⟨_, AST3.Expr.structInst _ none flds #[] false⟩ => do
    let mut cfg : Meta.Simp.Config := {}
    let mut discharger := none
    for (⟨_, n⟩, e) in flds do
      match n, e.kind with
      | `max_steps, Expr.nat n => cfg := {cfg with maxSteps := n}
      | `contextual, e => cfg := asBool e cfg fun cfg b => {cfg with contextual := b}
      | `zeta, e => cfg := asBool e cfg fun cfg b => {cfg with zeta := b}
      | `beta, e => cfg := asBool e cfg fun cfg b => {cfg with beta := b}
      | `eta, e => cfg := asBool e cfg fun cfg b => {cfg with eta := b}
      | `iota, e => cfg := asBool e cfg fun cfg b => {cfg with iota := b}
      | `proj, e => cfg := asBool e cfg fun cfg b => {cfg with proj := b}
      | `single_pass, e => cfg := asBool e cfg fun cfg b => {cfg with singlePass := b}
      | `memoize, e => cfg := asBool e cfg fun cfg b => {cfg with memoize := b}
      | `discharger, _ =>
          let disch ← Translate.trTactic (Spanned.dummy <| Tactic.expr e)
          discharger := some (← `(Lean.Parser.Tactic.discharger| (disch := $disch:tactic)))
      | _, _ => warn! "warning: unsupported simp config option: {n}"
    pure (cfg, discharger)
  | some _ => warn! "warning: unsupported simp config syntax" | pure (none, none)
where
  asBool {α} : AST3.Expr → α → (α → Bool → α) → α
  | AST3.Expr.const ⟨_, `tt⟩ _ _, a, f => f a true
  | AST3.Expr.const ⟨_, `ff⟩ _ _, a, f => f a false
  | _, a, _ => a

def quoteSimpConfig (cfg : Meta.Simp.Config) : Option Syntax := Id.run do
  if cfg == {} then return none
  let a := #[]
    |> push cfg {} qnat `maxSteps (·.maxSteps)
    |> push cfg {} qnat `maxDischargeDepth (·.maxDischargeDepth)
    |> push cfg {} qbool `contextual (·.contextual)
    |> push cfg {} qbool `memoize (·.memoize)
    |> push cfg {} qbool `singlePass (·.singlePass)
    |> push cfg {} qbool `zeta (·.zeta)
    |> push cfg {} qbool `beta (·.beta)
    |> push cfg {} qbool `eta (·.eta)
    |> push cfg {} qbool `iota (·.iota)
    |> push cfg {} qbool `proj (·.proj)
    |> push cfg {} qbool `decide (·.decide)
  `({ $[$(a.pop):structInstField ,]* $(a.back):structInstField })
where
  qbool (b : Bool) : Syntax := mkIdent $ cond b `true `false
  qnat : ℕ → Syntax := Quote.quote
  push {β} [BEq β] {α} (a b : α) (q : β → Syntax)
    (n : Name) (f : α → β) (args : Array Syntax) : Array Syntax := Id.run do
    if f a == f b then args else
      args.push <| Id.run `(Parser.Term.structInstField| $(mkIdent n):ident := $(q (f a)))

def trSimpLemma (e : Spanned AST3.Expr) : M Syntax :=
  return mkNode ``Parser.Tactic.simpLemma #[mkNullNode, ← trExpr e]

def mkConfigStx? (stx : Option Syntax) : M (Option Syntax) :=
  stx.mapM fun stx => `(Lean.Parser.Tactic.config| (config := $stx))

def mkConfigStx (stx : Option Syntax) : M Syntax :=
  mkOpt stx fun stx => `(Lean.Parser.Tactic.config| (config := $stx))

def trSimpArg : Parser.SimpArg → M Syntax
  | SimpArg.allHyps => pure $ mkNode ``Parser.Tactic.simpStar #[mkAtom "*"]
  | SimpArg.expr sym e =>
    return mkNode ``Parser.Tactic.simpLemma #[mkNullNode,
      mkNullNode (if sym then #[mkAtom "←"] else #[]), ← trExpr e]
  | SimpArg.except e =>
    return mkNode ``Parser.Tactic.simpErase #[mkAtom "-", ← mkIdentI e]

def trSimpArgs (hs : Array Parser.SimpArg) : M (Array Syntax) := hs.mapM trSimpArg

def filterSimpStar (hs : Array Syntax) : Array Syntax × Bool :=
  hs.foldl (init := (#[], false)) fun (out, all) stx =>
    if stx.isOfKind ``Parser.Tactic.simpStar then (out, true) else (out.push stx, all)

@[trTactic simp] def trSimp : TacM Syntax := do
  let iota ← parse (tk "!")?; let trace ← parse (tk "?")?
  if iota.isSome then warn! "warning: unsupported simp config option: iota_eqn"
  if trace.isSome then warn! "warning: unsupported simp config option: trace_lemmas"
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let (hs', all) := filterSimpStar hs
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent
  let loc ← parse location
  let (cfg, disch) ← parseSimpConfig (← expr?)
  let cfg ← mkConfigStx? (cfg.bind quoteSimpConfig)
  let simpAll := all && loc matches Location.wildcard
  match simpAll, attrs with
  | true, #[] =>
    `(tactic| simp_all $(cfg)? $(disch)? $[only%$o]? $[[$(hs'.asNonempty),*]]?)
  | false, #[] =>
    `(tactic| simp $(cfg)? $(disch)? $[only%$o]? $[[$(hs.asNonempty),*]]? $(← trLoc loc)?)
  | _, _ => do
    let simpAll := optTk simpAll
    `(tactic| simp' $[*%$simpAll]? $(cfg)? $(disch)? $[only%$o]?
      $[[$(hs.asNonempty),*]]? $[with $(attrs.asNonempty)*]? $(← trLoc loc)?)

@[trTactic trace_simp_set] def trTraceSimpSet : TacM Syntax := do
  let o ← parse onlyFlag
  let hs ← parse simpArgList
  let attrs ← parse withIdentList
  warn! "unsupported: trace_simp_set"

@[trTactic simp_intros] def trSimpIntros : TacM Syntax := do
  let ids := (← parse ident_*).map trIdent_
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let cfg := (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(tactic| simp_intro $[(config := $cfg)]? $ids* $[only%$o]? $[[$hs,*]]? $[with $attrs*]?)

@[trTactic dsimp] def trDSimp : TacM Syntax := do
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let loc ← trLoc (← parse location)
  let cfg := (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(tactic| dsimp' $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]? $[with $attrs*]? $(loc)?)

@[trTactic reflexivity refl] def trRefl : TacM Syntax := `(tactic| rfl)
@[trNITactic tactic.interactive.refl] def trNIRefl (_ : AST3.Expr) : M Syntax := `(tactic| rfl)

@[trTactic symmetry] def trSymmetry : TacM Syntax := `(tactic| symm)

@[trTactic transitivity] def trTransitivity : TacM Syntax := do
  `(tactic| trans $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

@[trTactic ac_reflexivity ac_refl] def trACRefl : TacM Syntax := `(tactic| ac_rfl)

@[trTactic cc] def trCC : TacM Syntax := `(tactic| cc)

@[trTactic subst] def trSubst : TacM Syntax := do
  `(tactic| subst $(← trExpr (← parse pExpr)))

@[trTactic subst_vars] def trSubstVars : TacM Syntax := `(tactic| subst_vars)

@[trTactic clear] def trClear : TacM Syntax := do
  match ← parse ident* with
  | #[] => `(tactic| skip)
  | ids => `(tactic| clear $[$(ids.map mkIdent)]*)

@[trTactic dunfold] def trDUnfold : TacM Syntax := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg ← mkConfigStx? $ (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  let cs ← liftM $ cs.mapM mkIdentI
  `(tactic| dunfold $[$cfg:config]? $[$cs:ident]* $[$(← trLoc loc):location]?)

@[trTactic delta] def trDelta : TacM Syntax := do
  `(tactic| delta' $(← liftM $ (← parse ident*).mapM mkIdentI)* $[$(← trLoc (← parse location))]?)

@[trTactic unfold_projs] def trUnfoldProjs : TacM Syntax := do
  let loc ← parse location
  let cfg ← mkConfigStx? $ (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(tactic| unfold_projs $[$cfg:config]? $[$(← trLoc loc):location]?)

@[trTactic unfold] def trUnfold : TacM Syntax := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg ← mkConfigStx? $ (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  let cs ← liftM $ cs.mapM mkIdentI
  `(tactic| unfold $[$cfg:config]? $[$cs:ident]* $[$(← trLoc loc):location]?)

@[trTactic unfold1] def trUnfold1 : TacM Syntax := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg ← mkConfigStx? $ (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  let cs ← liftM $ cs.mapM mkIdentI
  `(tactic| unfold1 $[$cfg:config]? $[$cs:ident]* $[$(← trLoc loc):location]?)

@[trTactic apply_opt_param] def trApplyOptParam : TacM Syntax := `(tactic| infer_opt_param)

@[trTactic apply_auto_param] def trApplyAutoParam : TacM Syntax := `(tactic| infer_auto_param)

@[trTactic fail_if_success success_if_fail] def trFailIfSuccess : TacM Syntax := do
  `(tactic| fail_if_success $(← trBlock (← itactic)):tacticSeq)

@[trTactic guard_expr_eq] def trGuardExprEq : TacM Syntax := do
  `(tactic| guard_expr $(← trExpr (← expr!)) =ₐ $(← trExpr (← parse (tk ":=" *> pExpr))))

@[trTactic guard_target] def trGuardTarget : TacM Syntax := do
  `(tactic| guard_target =ₐ $(← trExpr (← parse pExpr)))

@[trTactic guard_hyp] def trGuardHyp : TacM Syntax := do
  `(tactic| guard_hyp $(mkIdent (← parse ident))
    $[:ₐ $(← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr)]?
    $[:=ₐ $(← liftM $ (← parse (tk ":=" *> pExpr)?).mapM trExpr)]?)

@[trTactic match_target] def trMatchTarget : TacM Syntax := do
  let t ← trExpr (← parse pExpr)
  let m ← expr?
  if m.isSome then warn! "warning: unsupported: match_target reducibility"
  `(tactic| match_target $t)

@[trTactic by_cases] def trByCases : TacM Syntax := do
  let (n, q) ← parse casesArg
  let q ← trExpr q
  `(tactic| by_cases' $[$(n.map mkIdent) :]? $q)

@[trTactic funext] def trFunext : TacM Syntax := do
  `(tactic| funext $[$((← parse ident_*).map trBinderName)]*)

@[trTactic by_contradiction by_contra] def trByContra : TacM Syntax := do
  `(tactic| by_contra $((← parse (ident)?).map mkIdent)?)

@[trTactic type_check] def trTypeCheck : TacM Syntax := do
  `(tactic| type_check $(← trExpr (← parse pExpr)))

@[trTactic done] def trDone : TacM Syntax := do `(tactic| done)

@[trTactic «show»] def trShow : TacM Syntax := do `(tactic| show $(← trExpr (← parse pExpr)))

@[trTactic specialize] def trSpecialize : TacM Syntax := do
  let (head, args) ← trAppArgs (← parse pExpr) fun e =>
    match e.kind.unparen with
    | Expr.ident h => pure h
    | Expr.«@» false ⟨_, Expr.ident h⟩ =>
      warn! "unsupported: specialize @hyp" | pure h
    | _ => warn! "unsupported: specialize non-hyp"
  `(tactic| specialize $(Syntax.mkApp (mkIdent head) args))

@[trTactic congr] def trCongr : TacM Syntax := do `(tactic| congr)

@[trTactic rsimp] def trRSimp : TacM Syntax := do `(tactic| rsimp)

@[trTactic comp_val] def trCompVal : TacM Syntax := do `(tactic| comp_val)

@[trTactic async] def trAsync : TacM Syntax := do
  `(tactic| async $(← trBlock (← itactic)):tacticSeq)

@[trTactic conv] def trConvTac : TacM Syntax := do
  `(tactic| conv
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr)]?
    => $(← trConvBlock (← itactic)):convSeq)

@[trConv conv] def trConvConv : TacM Syntax := do
  `(conv| conv => $(← trConvBlock (← itactic)):convSeq)

@[trConv skip] def trSkipConv : TacM Syntax := `(conv| skip)

@[trConv whnf] def trWhnfConv : TacM Syntax := `(conv| whnf)

@[trConv dsimp] def trDSimpConv : TacM Syntax := do
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let cfg := (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(conv| dsimp $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]? $[with $attrs*]?)

@[trConv trace_lhs] def trTraceLHSConv : TacM Syntax := `(conv| trace_lhs)

@[trConv change] def trChangeConv : TacM Syntax := do
  `(conv| change $(← trExpr (← parse pExpr)))

@[trConv congr] def trCongrConv : TacM Syntax := `(conv| congr)

@[trConv funext] def trFunextConv : TacM Syntax := `(conv| ext)

@[trConv to_lhs] def trToLHSConv : TacM Syntax := `(conv| lhs)

@[trConv to_rhs] def trToRHSConv : TacM Syntax := `(conv| rhs)

@[trConv done] def trDoneConv : TacM Syntax := `(conv| done)

@[trConv find] def trFindConv : TacM Syntax := do
  -- TODO: parse conv itactic FIXME
  `(conv| find $(← trExpr (← parse pExpr)) => $(← trBlock (← itactic)):convSeq)

@[trConv «for»] def trForConv : TacM Syntax := do
  `(conv| for $(← trExpr (← parse pExpr))
    [$((← parse (listOf smallNat)).map Quote.quote),*]
    => $(← trBlock (← itactic)):tacticSeq)

@[trConv simp] def trSimpConv : TacM Syntax := do
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent
  let (cfg, disch) ← parseSimpConfig (← expr?)
  let cfg ← mkConfigStx? (cfg.bind quoteSimpConfig)
  match attrs with
  | #[] => `(tactic| simp $(cfg)? $(disch)? $[only%$o]? $[[$hs,*]]?)
  | _ => `(tactic| simp' $(cfg)? $(disch)? $[only%$o]? $[[$hs,*]]? with $attrs*)

@[trConv guard_lhs] def trGuardLHSConv : TacM Syntax := do
  `(conv| guard_lhs =ₐ $(← trExpr (← parse pExpr)))

@[trConv rewrite rw] def trRwConv : TacM Syntax := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  if let some cfg ← expr? then
    warn! "warning: unsupported: rw with cfg: {repr cfg}"
  `(conv| rw [$q,*])

section

variable (input : String) (p : ParserM α)

private partial def getChunk (acc : String) (i : String.Pos) : Bool × String.Pos × String :=
  if input.atEnd i then (false, i, acc) else
  let c := input.get i
  let i := input.next i
  if c == '{' then
    if input.get i == '{' then
      getChunk (acc ++ "\\{") (input.next i)
    else
      (true, i, acc)
  else
    getChunk (acc.push c) i

private partial def parseChunks [Repr α] (acc : String) (i : String.Pos)
  (out : Array (Sum String α)) : ParserM (Array (Sum String α)) := do
  let (next, i, acc) := getChunk input acc i
  if next then
    let (a, sz) ← withInput p
    let i := i + ⟨sz⟩
    guard (input.get i == '}'); let i := input.next i
    parseChunks "}" i (out.push (Sum.inl (acc.push '{')) |>.push (Sum.inr a))
  else
    pure $ out.push (Sum.inl (acc.push '\"'))

private partial def getStr : AST3.Expr → M String
  | Expr.string s => pure s
  | Expr.notation n #[⟨_, Arg.expr s1⟩, ⟨_, Arg.expr s2⟩] => do
    if n.name == `«expr ++ » then
      pure $ (← getStr s1.unparen) ++ (← getStr s2.unparen)
    else warn! "unsupported: interpolated non string literal"
  | _ => warn! "unsupported: interpolated non string literal"

def trInterpolatedStr (f : Syntax → TacM Syntax := pure) : TacM Syntax := do
  let s ← getStr (← expr!).kind.unparen
  let chunks ← parse $ parseChunks s pExpr "\"" 0 #[]
  mkNode interpolatedStrKind <$> chunks.mapM fun
    | Sum.inl s => pure $ Syntax.mkLit interpolatedStrLitKind s
    | Sum.inr e => trExpr e >>= f

end

@[trUserNota format_macro] def trFormatMacro : TacM Syntax := do `(f! $(← trInterpolatedStr))
@[trUserNota sformat_macro] def trSFormatMacro : TacM Syntax := do `(s! $(← trInterpolatedStr))

@[trTactic min_tac] def trMinTac : TacM Syntax := do
  -- wrong, but better than breakage
  `(tactic| exact minTac $(← trExpr (← parse pExpr)) $(← trExpr (← parse pExpr)))

@[trNITactic control_laws_tac] def trControlLawsTac (_ : AST3.Expr) : M Syntax :=
  `(tactic| (intros; rfl))

@[trTactic blast_disjs] def trBlastDisjs : TacM Syntax := `(tactic| cases_type* or)
