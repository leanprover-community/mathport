/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate
open AST3 Mathport.Translate.Parser

def mkConvBlock (args : Array Syntax.Conv) : TSyntax ``Parser.Tactic.Conv.convSeq :=
  mkNode ``Parser.Tactic.Conv.convSeq #[mkNode ``Parser.Tactic.Conv.convSeq1Indented #[
    mkNullNode.mkSep args]]

mutual

  partial def trConvBlock : Block → M (TSyntax ``Parser.Tactic.Conv.convSeq)
    | ⟨_, none, none, #[]⟩ => return mkConvBlock #[← `(conv| skip)]
    | ⟨_, none, none, tacs⟩ => mkConvBlock <$> tacs.mapM trConv
    | ⟨_, _cl, _cfg, _tacs⟩ => warn! "unsupported (TODO): conv block with cfg"

  partial def trConv : Spanned Tactic → M Syntax.Conv := spanningS fun
    | Tactic.block bl => do `(conv| · $(← trConvBlock bl):convSeq)
    | Tactic.by tac => do `(conv| · $(← trConv tac):conv)
    | Tactic.«;» _tacs => warn! "unsupported (impossible)"
    | Tactic.«<|>» tacs => do
      `(conv| first $[| $(← tacs.mapM trConv):conv]*)
    | Tactic.«[]» _tacs => warn! "unsupported (impossible)"
    | Tactic.exact_shortcut _ => warn! "unsupported (impossible)"
    | Tactic.expr e => do
      match ← trExpr e with
      | `(do $[$els]*) => `(conv| run_conv $[$els:doSeqItem]*)
      | stx => `(conv| run_conv $stx:term)
    | Tactic.interactive n args => do
      match (← get).convs.find? n with
      | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
      | none => warn! "unsupported conv tactic {repr n}"

end

namespace Tactic

def trLoc : (loc : Location) → M (Option (TSyntax ``Parser.Tactic.location))
  | Location.wildcard => some <$> `(Parser.Tactic.location| at *)
  | Location.targets #[] false => warn! "unsupported"
  | Location.targets #[] true => pure none
  | Location.targets hs goal =>
    let hs : Array Term := hs.map (⟨·⟩)
    let goal := optTk goal
    some <$> `(Parser.Tactic.location| at $[$hs]* $[⊢%$goal]?)

@[tr_tactic propagate_tags] def trPropagateTags : TacM Syntax.Tactic := do
  `(tactic| propagate_tags $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic intro] def trIntro : TacM Syntax.Tactic := do
  match ← parse (ident_)? with
  | some (BinderName.ident h) => `(tactic| intro $(mkIdent h):ident)
  | _ => `(tactic| intro)

@[tr_tactic intros] def trIntros : TacM Syntax.Tactic := do
  match ← parse ident_* with
  | #[] => `(tactic| intros)
  | hs => `(tactic| intro $[$(hs.map trIdent_)]*)

@[tr_tactic introv] def trIntrov : TacM Syntax.Tactic := do
  `(tactic| introv $((← parse ident_*).map trBinderIdent)*)

@[tr_tactic rename] def trRename : TacM Syntax.Tactic := do
  let renames ← parse renameArgs
  let as := renames.map fun (a, _) => mkIdent a
  let bs := renames.map fun (_, b) => mkIdent b
  `(tactic| rename' $[$as:ident => $bs],*)

@[tr_tactic apply] def trApply : TacM Syntax.Tactic := do
  `(tactic| apply $(← trExpr (← parse pExpr)))

@[tr_tactic fapply] def trFApply : TacM Syntax.Tactic := do
  `(tactic| fapply $(← trExpr (← parse pExpr)))

@[tr_tactic eapply] def trEApply : TacM Syntax.Tactic := do
  `(tactic| eapply $(← trExpr (← parse pExpr)))

@[tr_tactic apply_with] def trApplyWith : TacM Syntax.Tactic := do
  let expr ← trExpr (← parse pExpr)
  let cfg ← trExpr (← expr!)
  `(tactic| apply (config := $cfg) $expr)

@[tr_tactic mapply] def trMApply : TacM Syntax.Tactic := do
  `(tactic| mapply $(← trExpr (← parse pExpr)))

@[tr_tactic apply_instance] def trApplyInstance : TacM Syntax.Tactic := `(tactic| infer_instance)
@[tr_ni_tactic tactic.apply_instance] def trNIApplyInstance (_ : AST3.Expr) : M Syntax.Tactic :=
  `(tactic| infer_instance)

@[tr_tactic refine] def trRefine : TacM Syntax.Tactic := do
  `(tactic| refine' $(← trExpr (← parse pExpr)))

@[tr_tactic assumption] def trAssumption : TacM Syntax.Tactic := do `(tactic| assumption)
@[tr_ni_tactic tactic.assumption] def trNIAssumption (_ : AST3.Expr) : M Syntax.Tactic :=
  `(tactic| assumption)

@[tr_tactic assumption'] def trAssumption' : TacM Syntax.Tactic := do `(tactic| assumption')

@[tr_tactic change] def trChange : TacM Syntax.Tactic := do
  let q ← trExpr (← parse pExpr)
  let h ← parse (tk "with" *> pExpr)?
  let loc ← trLoc (← parse location)
  match h with
  | none => `(tactic| change $q $[$loc]?)
  | some h => `(tactic| change $q with $(← trExpr h) $[$loc]?)

@[tr_tactic exact «from»] def trExact : TacM Syntax.Tactic := do
  `(tactic| exact $(← trExpr (← parse pExpr)))

@[tr_tactic exacts] def trExacts : TacM Syntax.Tactic := do
  `(tactic| exacts [$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*])

@[tr_tactic revert] def trRevert : TacM Syntax.Tactic := do
  `(tactic| revert $[$((← parse ident*).map mkIdent)]*)

def trRwRule (r : RwRule) : M (TSyntax ``Parser.Tactic.rwRule) := do
  let e ← trExpr r.rule
  if r.symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)

def trRwArgs : TacM (Array (TSyntax ``Parser.Tactic.rwRule) × Option (TSyntax ``Parser.Tactic.location)) := do
  let q ← liftM $ (← parse rwRules).mapM trRwRule
  let loc ← trLoc (← parse location)
  if let some cfg ← expr? then
    warn! "warning: unsupported: rw with cfg: {repr cfg}"
  pure (q, loc)

@[tr_tactic rewrite rw] def trRw : TacM Syntax.Tactic := do
  let (q, loc) ← trRwArgs; `(tactic| rw [$q,*] $(loc)?)

@[tr_tactic rwa] def trRwA : TacM Syntax.Tactic := do
  let (q, loc) ← trRwArgs; `(tactic| rwa [$q,*] $(loc)?)

@[tr_tactic erewrite erw] def trERw : TacM Syntax.Tactic := do
  let (q, loc) ← trRwArgs; `(tactic| erw [$q,*] $(loc)?)

@[tr_tactic with_cases] def trWithCases : TacM Syntax.Tactic := do
  warn! "warning: unsupported: with_cases"
  trIdTactic (← itactic)

@[tr_tactic generalize] def trGeneralize : TacM Syntax.Tactic := do
  let h ← parse (ident)? <* parse (tk ":")
  let (e, x) ← parse generalizeArg
  `(tactic| generalize $[$(h.map mkIdent) :]? $(← trExpr e) = $(mkIdent x))

@[tr_tactic induction] def trInduction : TacM Syntax.Tactic := do
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

@[tr_tactic case] def trCase : TacM Syntax.Tactic := do
  let args ← parse case
  let tac ← trBlock (← itactic)
  let trCaseArg := fun (tags, xs) => do
    let tag ← tags.foldlM (init := Name.anonymous) fun
      | acc, .ident (.str _ id) => pure (acc.str id)
      | acc, tag => warn! "weird case tag {repr tag}" | pure acc
    let xs := xs.map trBinderIdent
    `(Parser.Tactic.caseArg| $(mkIdent tag):ident $xs*)
  `(tactic| case $(← args.mapM trCaseArg)|* => $tac:tacticSeq)

@[tr_tactic destruct] def trDestruct : TacM Syntax.Tactic := do
  `(tactic| destruct $(← trExpr (← parse pExpr)))

@[tr_tactic cases] def trCases : TacM Syntax.Tactic := do
  let (hp, e) ← parse casesArg
  let e ← trExpr e
  let ids ← parse withIdentList
  match ids with
  | #[] => `(tactic| cases $[$(hp.map mkIdent) :]? $e)
  | _ => `(tactic| cases' $[$(hp.map mkIdent) :]? $e with $(ids.map trBinderIdent)*)

@[tr_tactic cases_matching casesm] def trCasesM : TacM Syntax.Tactic := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| casesm $ps,*)
  | some () => `(tactic| casesm* $ps,*)

@[tr_tactic cases_type] def trCasesType : TacM Syntax.Tactic := do
  let bang ← parse (tk "!")?
  let star := optTk (← parse (tk "*")?).isSome
  let idents := (← parse ident*).map mkIdent
  if bang.isSome then
    `(tactic|cases_type! $[*%$star]? $[$idents]*)
  else
    `(tactic|cases_type $[*%$star]? $[$idents]*)

@[tr_tactic trivial] def trTrivial : TacM Syntax.Tactic := `(tactic| trivial)

@[tr_tactic admit «sorry»] def trSorry : TacM Syntax.Tactic := do
  match ← parse (Parser.itactic)? with
  | none => `(tactic| sorry)
  | some bl => `(tactic| stop $(← trBlock bl):tacticSeq)

@[tr_tactic contradiction] def trContradiction : TacM Syntax.Tactic := `(tactic| contradiction)

@[tr_tactic iterate] def trIterate : TacM Syntax.Tactic := do
  match ← parse (smallNat)?, ← trBlock (← itactic) with
  | none, tac => `(tactic| repeat $tac:tacticSeq)
  | some n, tac => `(tactic| iterate $(Quote.quote n) $tac:tacticSeq)

@[tr_tactic «repeat»] def trRepeat : TacM Syntax.Tactic := do
  `(tactic| repeat' $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic «try»] def trTry : TacM Syntax.Tactic := do
  `(tactic| try $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic skip] def trSkip : TacM Syntax.Tactic := `(tactic| skip)

@[tr_tactic solve1] def trSolve1 : TacM Syntax.Tactic := do
  `(tactic| · ($(← trBlock (← itactic)):tacticSeq))

@[tr_tactic abstract] def trAbstract : TacM Syntax.Tactic := do
  `(tactic| abstract $(← liftM $ (← parse (ident)?).mapM mkIdentF)?
      $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic all_goals] def trAllGoals : TacM Syntax.Tactic := do
  `(tactic| all_goals $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic any_goals] def trAnyGoals : TacM Syntax.Tactic := do
  `(tactic| any_goals $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic focus] def trFocus : TacM Syntax.Tactic := do
  `(tactic| focus $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic assume] def trAssume : TacM Syntax.Tactic := do
  match ← parse (Sum.inl <$> (tk ":" *> pExpr) <|> Sum.inr <$> parseBinders) with
  | Sum.inl ty => `(tactic| intro ($(mkIdent `this) : $(← trExpr ty)))
  | Sum.inr bis => `(tactic| intro $[$(← trIntroBinders bis)]*)
where
  trIntroBinder : Binder → M (Array Term)
  | Binder.binder _ none _ _ _ => return #[← `(_)]
  | Binder.binder _ (some vars) _ none _ =>
    return vars.map (trIdent_ ·.kind)
  | Binder.binder _ (some vars) bis (some ty) _ => do
    let ty ← trDArrow bis ty
    vars.mapM fun v => `(($(trIdent_ v.kind) : $ty))
  | Binder.collection _ _ _ _ => warn! "unsupported: assume with binder collection"
  | Binder.notation _ => warn! "unsupported: assume notation"

  trIntroBinders (bis : Array (Spanned Binder)) : M (Array Term) :=
    bis.concatMapM (trIntroBinder ·.kind)

@[tr_tactic «have»] def trHave : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| have $[$h:ident]? $[: $ty:term]? := $(← trExpr pr))
  | none => `(tactic| have $[$h:ident]? $[: $ty:term]?)

@[tr_tactic «let»] def trLet : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).filter (· != `this) |>.map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => match h with
    | some h => `(tactic| let $h:ident $[: $ty:term]? := $(← trExpr pr))
    | none => `(tactic| let this $[: $ty:term]? := $(← trExpr pr))
  | none =>
    `(tactic| let $[$h:ident]? $[: $ty:term]?)

@[tr_tactic «suffices»] def trSuffices : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  `(tactic| suffices $[$h:ident]? $[: $ty:term]?)

@[tr_tactic trace_state] def trTraceState : TacM Syntax.Tactic := `(tactic| trace_state)

@[tr_tactic trace] def trTrace : TacM Syntax.Tactic := do `(tactic| trace $(← trExpr (← expr!)):term)

@[tr_tactic existsi] def trExistsI : TacM Syntax.Tactic := do
  `(tactic| exists $(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*)

@[tr_tactic constructor] def trConstructor : TacM Syntax.Tactic := `(tactic| constructor)

@[tr_tactic econstructor] def trEConstructor : TacM Syntax.Tactic := `(tactic| econstructor)

@[tr_tactic left] def trLeft : TacM Syntax.Tactic := `(tactic| left)

@[tr_tactic right] def trRight : TacM Syntax.Tactic := `(tactic| right)

@[tr_tactic split] def trSplit : TacM Syntax.Tactic := `(tactic| constructor)

@[tr_tactic constructor_matching] def trConstructorM : TacM Syntax.Tactic := do
  let _rec ← parse (tk "*")?
  let ps ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  match _rec with
  | none => `(tactic| constructorm $ps,*)
  | some () => `(tactic| constructorm* $ps,*)

@[tr_tactic exfalso] def trExfalso : TacM Syntax.Tactic := `(tactic| exfalso)

@[tr_tactic injection] def trInjection : TacM Syntax.Tactic := do
  let e ← trExpr (← parse pExpr)
  let hs := (← parse withIdentList).map trIdent_' |>.asNonempty
  `(tactic| injection $e $[with $hs*]?)

@[tr_tactic injections] def trInjections : TacM Syntax.Tactic := do
  let hs := (← parse withIdentList).map trIdent_'
  `(tactic| injections $hs*)

def parseSimpConfig : Option (Spanned AST3.Expr) →
    M (Option Meta.Simp.Config × Option (TSyntax ``Parser.Tactic.discharger))
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

def quoteSimpConfig (cfg : Meta.Simp.Config) : Option Term := Id.run do
  if cfg == {} then return none
  --  `Quote Bool` fully qualifies true and false but we are trying to generate
  --  the unqualified form here.
  let _inst : Quote Bool := ⟨fun b => mkIdent (if b then `true else `false)⟩
  let a := #[]
    |> push cfg {} `maxSteps (·.maxSteps)
    |> push cfg {} `maxDischargeDepth (·.maxDischargeDepth)
    |> push cfg {} `contextual (·.contextual)
    |> push cfg {} `memoize (·.memoize)
    |> push cfg {} `singlePass (·.singlePass)
    |> push cfg {} `zeta (·.zeta)
    |> push cfg {} `beta (·.beta)
    |> push cfg {} `eta (·.eta)
    |> push cfg {} `iota (·.iota)
    |> push cfg {} `proj (·.proj)
    |> push cfg {} `decide (·.decide)
  `({ $[$a:structInstField],* })
where
  push {β} [BEq β] {α} (a b : α) [Quote β]
      (n : Name) (f : α → β) (args : Array (TSyntax ``Parser.Term.structInstField)) :
      Array (TSyntax ``Parser.Term.structInstField) := Id.run do
    if f a == f b then args else
      args.push <| Id.run `(Parser.Term.structInstField| $(mkIdent n):ident := $(quote (f a)))

def trSimpLemma (e : Spanned AST3.Expr) : M (TSyntax ``Parser.Tactic.simpLemma) := do
  `(Parser.Tactic.simpLemma| $(← trExpr e):term)

def mkConfigStx? (stx : Option Term) : M (Option (TSyntax ``Parser.Tactic.config)) :=
  stx.mapM fun stx => `(Lean.Parser.Tactic.config| (config := $stx))

def trSimpArg : Parser.SimpArg → M (TSyntax ``Parser.Tactic.simpArg)
  | .allHyps => `(Parser.Tactic.simpArg| *)
  | .expr false e => do `(Parser.Tactic.simpArg| $(← trExpr e):term)
  | .expr true e => do `(Parser.Tactic.simpArg| ← $(← trExpr e))
  | .except e => do `(Parser.Tactic.simpArg| - $(← mkIdentI e))

def trSimpExt [Coe (TSyntax ``Parser.Tactic.simpLemma) (TSyntax α)] (n : Name) : TSyntax α :=
  Id.run `(Parser.Tactic.simpLemma| $(mkIdent n):ident)

instance : Coe (TSyntax ``Parser.Tactic.simpLemma) (TSyntax ``Parser.Tactic.simpArg) where
  coe s := ⟨s⟩

-- AWFUL HACK: `(simp [$_]) gets wrong antiquotation type :-/
instance : Coe (TSyntax ``Parser.Tactic.simpArg) (TSyntax ``Parser.Tactic.simpStar) where
  coe s := ⟨s⟩

def trSimpArgs (hs : Array Parser.SimpArg) : M (Array (TSyntax ``Parser.Tactic.simpArg)) :=
  hs.mapM trSimpArg

def filterSimpStar (hs : Array (TSyntax ``Parser.Tactic.simpArg)) :
    Array (TSyntax [``Parser.Tactic.simpErase, ``Parser.Tactic.simpLemma]) × Bool :=
  hs.foldl (init := (#[], false)) fun (out, all) stx =>
    if stx.1.isOfKind ``Parser.Tactic.simpStar then (out, true) else (out.push ⟨stx⟩, all)

def trSimpCore (autoUnfold trace : Bool) : TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let (hs', all) := filterSimpStar hs
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let loc ← parse location
  let (cfg, disch) ← parseSimpConfig (← expr?)
  let cfg ← mkConfigStx? (cfg.bind quoteSimpConfig)
  let simpAll := all && loc matches Location.wildcard
  if simpAll then
    let hs' := (hs' ++ attrs.map trSimpExt).asNonempty
    match autoUnfold, trace with
    | true, true => `(tactic| simp_all?! $(cfg)? $(disch)? $[only%$o]? $[[$[$hs'],*]]?)
    | false, true => `(tactic| simp_all? $(cfg)? $(disch)? $[only%$o]? $[[$[$hs'],*]]?)
    | true, false => `(tactic| simp_all! $(cfg)? $(disch)? $[only%$o]? $[[$[$hs'],*]]?)
    | false, false => `(tactic| simp_all $(cfg)? $(disch)? $[only%$o]? $[[$[$hs'],*]]?)
  else
    let hs := (hs ++ attrs.map trSimpExt).asNonempty
    let loc ← trLoc loc
    match autoUnfold, trace with
    | true, true => `(tactic| simp?! $(cfg)? $(disch)? $[only%$o]? $[[$[$hs],*]]? $(loc)?)
    | false, true => `(tactic| simp? $(cfg)? $(disch)? $[only%$o]? $[[$[$hs],*]]? $(loc)?)
    | true, false => `(tactic| simp! $(cfg)? $(disch)? $[only%$o]? $[[$[$hs],*]]? $(loc)?)
    | false, false => `(tactic| simp $(cfg)? $(disch)? $[only%$o]? $[[$[$hs],*]]? $(loc)?)

@[tr_tactic simp] def trSimp : TacM Syntax.Tactic := do
  let autoUnfold ← parse (tk "!")?; let trace ← parse (tk "?")?
  trSimpCore autoUnfold.isSome trace.isSome

@[tr_tactic trace_simp_set] def trTraceSimpSet : TacM Syntax.Tactic := do
  let _o ← parse onlyFlag
  let _hs ← parse simpArgList
  let _attrs ← parse withIdentList
  warn! "unsupported: trace_simp_set"

@[tr_tactic simp_intros] def trSimpIntros : TacM Syntax.Tactic := do
  let ids := (← parse ident_*).map trBinderIdent
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let cfg := (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(tactic| simp_intro $[(config := $cfg)]? $[$ids]* $[only%$o]? $[[$hs,*]]?)

def trDSimpCore (autoUnfold trace : Bool) (parseCfg : TacM (Option (Spanned AST3.Expr))) :
    TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let (hs, _all) := filterSimpStar hs -- dsimp [*] is always pointless
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let loc ← trLoc (← parse location)
  let cfg := (← parseSimpConfig (← parseCfg)).1.bind quoteSimpConfig
  match autoUnfold, trace with
  | true, true => `(tactic| dsimp?! $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]? $(loc)?)
  | false, true => `(tactic| dsimp? $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]? $(loc)?)
  | true, false => `(tactic| dsimp! $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]? $(loc)?)
  | false, false => `(tactic| dsimp $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]? $(loc)?)

@[tr_tactic dsimp] def trDSimp : TacM Syntax.Tactic := trDSimpCore false false expr?

@[tr_tactic reflexivity refl] def trRefl : TacM Syntax.Tactic := `(tactic| rfl)
@[tr_ni_tactic tactic.interactive.refl]
def trNIRefl (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| rfl)

@[tr_tactic symmetry] def trSymmetry : TacM Syntax.Tactic := `(tactic| symm)

@[tr_tactic transitivity] def trTransitivity : TacM Syntax.Tactic := do
  `(tactic| trans $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?)

@[tr_tactic ac_reflexivity ac_refl] def trACRefl : TacM Syntax.Tactic := `(tactic| ac_rfl)

@[tr_tactic cc] def trCC : TacM Syntax.Tactic := `(tactic| cc)

@[tr_tactic subst] def trSubst : TacM Syntax.Tactic := do
  `(tactic| subst $(← trExpr (← parse pExpr)))

@[tr_tactic subst_vars] def trSubstVars : TacM Syntax.Tactic := `(tactic| subst_vars)

@[tr_tactic clear] def trClear : TacM Syntax.Tactic := do
  match ← parse ident* with
  | #[] => `(tactic| skip)
  | ids => `(tactic| clear $[$(ids.map mkIdent)]*)

@[tr_tactic dunfold] def trDUnfold : TacM Syntax.Tactic := do
  let cs ← parse ident*
  let loc ← parse location
  let cfg ← mkConfigStx? $ (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  let cs ← liftM $ cs.mapM mkIdentI
  `(tactic| dsimp $[$cfg:config]? only [$[$cs:ident],*] $[$(← trLoc loc):location]?)

@[tr_tactic delta] def trDelta : TacM Syntax.Tactic := do
  `(tactic| delta $(← liftM $ (← parse ident*).mapM mkIdentI)* $[$(← trLoc (← parse location))]?)

@[tr_tactic unfold_projs] def trUnfoldProjs : TacM Syntax.Tactic := do
  let loc ← parse location
  let cfg ← mkConfigStx? $ (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(tactic| unfold_projs $[$cfg:config]? $[$(← trLoc loc):location]?)

@[tr_tactic unfold] def trUnfold : TacM Syntax.Tactic := do
  let cs ← parse ident*
  let loc ← parse location
  if (← expr?).isSome then warn! "warning: unsupported: unfold config"
  let cs ← liftM $ cs.mapM mkIdentI
  `(tactic| unfold $[$cs:ident]* $[$(← trLoc loc):location]?)

@[tr_tactic unfold1] def trUnfold1 : TacM Syntax.Tactic := do
  let cs ← parse ident*
  let loc ← parse location
  if (← expr?).isSome then warn! "warning: unsupported: unfold config"
  let cs ← liftM $ cs.mapM mkIdentI
  let loc ← trLoc loc
  let tac ← cs.mapM fun c => `(tactic| unfold $c:ident $[$loc:location]?)
  match tac with
  | #[tac] => pure tac
  | _ => `(tactic| first $[| $tac:tactic]*)

@[tr_tactic apply_opt_param apply_auto_param]
def trInferParam : TacM Syntax.Tactic := `(tactic| infer_param)

@[tr_tactic fail_if_success success_if_fail] def trFailIfSuccess : TacM Syntax.Tactic := do
  `(tactic| fail_if_success $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic guard_expr_eq] def trGuardExprEq : TacM Syntax.Tactic := do
  `(tactic| guard_expr $(← trExpr (← expr!)) =ₐ $(← trExpr (← parse (tk ":=" *> pExpr))))

@[tr_tactic guard_target] def trGuardTarget : TacM Syntax.Tactic := do
  `(tactic| guard_target =ₐ $(← trExpr (← parse pExpr)))

@[tr_tactic guard_hyp] def trGuardHyp : TacM Syntax.Tactic := do
  `(tactic| guard_hyp $(mkIdent (← parse ident))
    $[:ₐ $(← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr)]?
    $[:=ₐ $(← liftM $ (← parse (tk ":=" *> pExpr)?).mapM trExpr)]?)

@[tr_tactic match_target] def trMatchTarget : TacM Syntax.Tactic := do
  let t ← trExpr (← parse pExpr)
  let m ← expr?
  if m.isSome then warn! "warning: unsupported: match_target reducibility"
  `(tactic| match_target $t)

@[tr_tactic by_cases] def trByCases : TacM Syntax.Tactic := do
  let (n, q) ← parse casesArg
  let q ← trExpr q
  `(tactic| by_cases $[$(n.map mkIdent) :]? $q)

@[tr_tactic funext] def trFunext : TacM Syntax.Tactic := do
  `(tactic| funext $[$((← parse ident_*).map trIdent_)]*)

@[tr_tactic by_contradiction by_contra] def trByContra : TacM Syntax.Tactic := do
  `(tactic| by_contra $[$((← parse (ident)?).map mkIdent):ident]?)

@[tr_tactic type_check] def trTypeCheck : TacM Syntax.Tactic := do
  `(tactic| type_check $(← trExpr (← parse pExpr)))

@[tr_tactic done] def trDone : TacM Syntax.Tactic := do `(tactic| done)

@[tr_tactic «show»] def trShow : TacM Syntax.Tactic := do `(tactic| show $(← trExpr (← parse pExpr)))

@[tr_tactic specialize] def trSpecialize : TacM Syntax.Tactic := do
  let (head, args) ← trAppArgs (← parse pExpr) fun e =>
    match e.kind.unparen with
    | Expr.ident h => pure h
    | Expr.«@» false ⟨_, Expr.ident h⟩ =>
      warn! "unsupported: specialize @hyp" | pure h
    | _ => warn! "unsupported: specialize non-hyp"
  `(tactic| specialize $(Syntax.mkApp (mkIdent head) args))

@[tr_tactic congr] def trCongr : TacM Syntax.Tactic := do `(tactic| congr)

@[tr_tactic rsimp] def trRSimp : TacM Syntax.Tactic := do `(tactic| rsimp)

@[tr_tactic comp_val] def trCompVal : TacM Syntax.Tactic := do `(tactic| comp_val)

@[tr_tactic async] def trAsync : TacM Syntax.Tactic := do
  `(tactic| async $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic conv] def trConvTac : TacM Syntax.Tactic := do
  `(tactic| conv
    $[at $((← parse (tk "at" *> ident)?).map mkIdent)]?
    $[in $(← liftM $ (← parse (tk "in" *> pExpr)?).mapM trExpr):term]?
    => $(← trConvBlock (← itactic)):convSeq)

@[tr_conv conv] def trConvConv : TacM Syntax.Conv := do
  `(conv| conv => $(← trConvBlock (← itactic)):convSeq)

@[tr_conv skip] def trSkipConv : TacM Syntax.Conv := `(conv| skip)

@[tr_conv whnf] def trWhnfConv : TacM Syntax.Conv := `(conv| whnf)

@[tr_conv dsimp] def trDSimpConv : TacM Syntax.Conv := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let (hs, _all) := filterSimpStar hs -- dsimp [*] is always pointless
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let cfg := (← parseSimpConfig (← expr?)).1.bind quoteSimpConfig
  `(conv| dsimp $[(config := $cfg)]? $[only%$o]? $[[$hs,*]]?)

@[tr_conv trace_lhs] def trTraceLHSConv : TacM Syntax.Conv := `(conv| trace_state)

@[tr_conv change] def trChangeConv : TacM Syntax.Conv := do
  `(conv| change $(← trExpr (← parse pExpr)))

@[tr_conv congr] def trCongrConv : TacM Syntax.Conv := `(conv| congr)

@[tr_conv funext] def trFunextConv : TacM Syntax.Conv := `(conv| ext)

@[tr_conv to_lhs] def trToLHSConv : TacM Syntax.Conv := `(conv| lhs)

@[tr_conv to_rhs] def trToRHSConv : TacM Syntax.Conv := `(conv| rhs)

@[tr_conv done] def trDoneConv : TacM Syntax.Conv := `(conv| done)

@[tr_conv find] def trFindConv : TacM Syntax.Conv := do
  `(conv| (pattern $(← trExpr (← parse pExpr)):term; ($(← trConvBlock (← itactic)):convSeq)))

@[tr_conv «for»] def trForConv : TacM Syntax.Conv := do
  let pat ← trExpr (← parse pExpr)
  let occs ← parse (listOf smallNat)
  let tac ← trConvBlock (← itactic)
  `(conv| pattern (occs := $[$(occs.map quote):num]*) $pat:term <;> ($tac))

@[tr_conv simp] def trSimpConv : TacM Syntax.Conv := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let (cfg, disch) ← parseSimpConfig (← expr?)
  let cfg ← mkConfigStx? (cfg.bind quoteSimpConfig)
  `(conv| simp $(cfg)? $(disch)? $[only%$o]? $[[$hs,*]]?)

@[tr_conv guard_lhs] def trGuardLHSConv : TacM Syntax.Conv := do
  `(conv| guard_target =ₐ $(← trExpr (← parse pExpr)))

@[tr_conv rewrite rw] def trRwConv : TacM Syntax.Conv := do
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

open TSyntax.Compat in
def trInterpolatedStr (f : Syntax → TacM Syntax := pure) : TacM (TSyntax interpolatedStrKind) := do
  let s ← getStr (← expr!).kind.unparen
  let chunks ← parse $ parseChunks s pExpr "\"" 0 #[]
  mkNode interpolatedStrKind <$> chunks.mapM fun
    | Sum.inl s => pure (Syntax.mkLit interpolatedStrLitKind s).1
    | Sum.inr e => do f (← trExpr e)

end

@[tr_user_nota format_macro] def trFormatMacro : TacM Syntax.Term := do
  `(f! $(← trInterpolatedStr))
@[tr_user_nota sformat_macro] def trSFormatMacro : TacM Syntax.Term := do
  `(s! $(← trInterpolatedStr))

@[tr_tactic min_tac] def trMinTac : TacM Syntax.Tactic := do
  -- wrong, but better than breakage
  `(tactic| exact minTac $(← trExpr (← parse pExpr)) $(← trExpr (← parse pExpr)))

@[tr_ni_tactic control_laws_tac] def trControlLawsTac (_ : AST3.Expr) : M Syntax.Tactic :=
  `(tactic| (intros; rfl))

@[tr_tactic blast_disjs] def trBlastDisjs : TacM Syntax.Tactic := `(tactic| cases_type* or)

