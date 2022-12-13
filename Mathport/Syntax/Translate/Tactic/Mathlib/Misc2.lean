/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3
import Mathport.Syntax.Translate.Tactic.Mathlib.Cache

-- Misc. special-purpose tactics

open Lean

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.trunc_cases
@[tr_tactic trunc_cases] def trTruncCases : TacM Syntax.Tactic := do
  `(tactic| trunc_cases $(← trExpr (← parse pExpr))
    $[with $(((← parse withIdentList).map trBinderIdent).asNonempty)*]?)

-- # tactic.abel
@[tr_tactic abel1] def trAbel1 : TacM Syntax.Tactic := do
  match ← parse (tk "!")? with
  | none => `(tactic| abel1)
  | some _ => `(tactic| abel1!)

@[tr_tactic abel] def trAbel : TacM Syntax.Tactic := do
  match ← parse (tk "!")?, ← parse (ident)?, ← trLoc (← parse location) with
  | none, none, loc => `(tactic| abel $[$loc:location]?)
  | none, some `raw, loc => `(tactic| abel raw $(loc)?)
  | none, some `term, loc => `(tactic| abel term $(loc)?)
  | some _, none, loc => `(tactic| abel! $[$loc:location]?)
  | some _, some `raw, loc => `(tactic| abel! raw $(loc)?)
  | some _, some `term, loc => `(tactic| abel! term $(loc)?)
  | _, _, _ => warn! "bad abel mode"

open TSyntax.Compat in
private def mkConfigStx (stx : Option Syntax) : M Syntax :=
  mkOpt stx fun stx => `(Lean.Parser.Tactic.config| (config := $stx))

open Mathlib.Tactic.LinearCombination in
def parseLinearComboConfig : Option (Spanned AST3.Expr) → M (Option Syntax.Tactic)
  | none => pure none
  | some ⟨_, AST3.Expr.«{}»⟩ => pure none
  | some ⟨_, AST3.Expr.structInst _ none flds #[] false⟩ => do
    let mut normalize := true
    let mut norm? := none
    for (⟨_, n⟩, e) in flds do
      match n, e.kind with
      | `normalize, e => normalize := parseSimpConfig.asBool e normalize fun _ b => b
      | `normalization_tactic, _ =>
        norm? ← Translate.trTactic (Spanned.dummy <| Tactic.expr e)
      | _, _ => warn! "warning: unsupported linear_combination config option: {n}"
    pure <| if normalize then norm? else some (← `(tactic| skip))
  | some _ => warn! "warning: unsupported linear_combination config syntax" | pure none

-- # tactic.linear_combination
@[tr_tactic linear_combination] def trLinearCombination : TacM Syntax.Tactic := do
  let e ← liftM $ (← parse (pExpr)? <* parse (tk "with")?).mapM trExpr
  `(tactic| linear_combination $[(norm := $(← parseLinearComboConfig (← expr?)))]? $[$e]?)

-- # tactic.noncomm_ring
@[tr_tactic noncomm_ring] def trNoncommRing : TacM Syntax.Tactic := `(tactic| noncomm_ring)

-- # tactic.omega
@[tr_tactic omega] def trOmega : TacM Syntax.Tactic := do
  let args ← parse ident*
  pure ⟨mkNode ``Parser.Tactic.omega #[mkAtom "omega",
    mkNullNode $ if args.contains `manual then #[mkAtom "manual"] else #[],
    mkNullNode $
      if args.contains `int then #[mkAtom "int"] else
      if args.contains `nat then #[mkAtom "nat"] else #[]]⟩

-- # tactic.fin_cases
@[tr_tactic fin_cases] def trFinCases : TacM Syntax.Tactic := do
  let hyp ← parse $ (tk "*" *> pure none) <|> (some <$> ident)
  let w ← liftM $ (← parse (tk "with" *> pExpr)?).mapM trExpr
  if let some u ← parse (tk "using" *> ident)? then
    warn! "warning: unsupported fin_cases 'using {u}' clause"
  match hyp with
  | none => `(tactic| fin_cases * $[with $w]?)
  | some h => `(tactic| fin_cases $(mkIdent h):ident $[with $w]?)

-- # tactic.interval_cases
@[tr_tactic interval_cases] def trIntervalCases : TacM Syntax.Tactic :=
  return ⟨mkNode ``Parser.Tactic.intervalCases #[mkAtom "interval_cases",
    ← mkOpt (← parse (pExpr)?) (fun e => return (← trExpr e).1),
    ← mkOptionalNodeM (← parse (tk "using" *> return (← ident, ← ident))?) fun (x, y) =>
      return #[mkAtom "using", mkIdent x, mkAtom ",", mkIdent y],
    mkOptionalNode' (← parse (tk "with" *> ident)?) fun h => #[mkAtom "with", mkIdent h]]⟩

-- # tactic.subtype_instance
@[tr_tactic subtype_instance] def trSubtypeInstance : TacM Syntax.Tactic := `(tactic| subtype_instance)

-- # tactic.derive_fintype

-- # tactic.group
@[tr_tactic group] def trGroup : TacM Syntax.Tactic := do
  `(tactic| group $(← trLoc (← parse location))?)

-- # tactic.cancel_denoms
@[tr_tactic cancel_denoms] def trCancelDenoms : TacM Syntax.Tactic := do
  `(tactic| cancel_denoms $(← trLoc (← parse location))?)

-- # tactic.transport
@[tr_tactic transport] def trTransport : TacM Syntax.Tactic := do
  `(tactic| transport
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?
    using $(← trExpr (← parse (tk "using" *> pExpr))))

-- # tactic.unfold_cases
@[tr_tactic unfold_cases] def trUnfoldCases : TacM Syntax.Tactic := do
  `(tactic| unfold_cases $(← trBlock (← itactic)):tacticSeq)

-- # tactic.field_simp
@[tr_tactic field_simp] def trFieldSimp : TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  let loc ← trLoc (← parse location)
  let (cfg, disch) ← parseSimpConfig (← expr?)
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  `(tactic| field_simp $(cfg)? $(disch)? $[only%$o]? $[[$hs,*]]? $(loc)?)

-- # tactic.equiv_rw

@[tr_tactic equiv_rw] def trEquivRw : TacM Syntax.Tactic := do
  let es ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  let loc ← trLoc (← parse location)
  let cfg ← liftM $ (← expr?).mapM trExpr
  match es with
  | #[e] => `(tactic| equiv_rw $[(config := $cfg)]? $e $[$loc]?)
  | _ => `(tactic| equiv_rw $[(config := $cfg)]? [$es,*] $[$loc]?)

@[tr_tactic equiv_rw_type] def trEquivRwType : TacM Syntax.Tactic := do
  let e ← trExpr (← parse pExpr)
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| equiv_rw_type $[(config := $cfg)]? $e)

-- # tactic.nth_rewrite
-- The indexing scheme for occurrences has changed between
-- mathlib3 and mathlib4, so we need to increment here.
-- See https://github.com/leanprover-community/mathlib4/pull/823

@[tr_tactic nth_rewrite] def trNthRewrite : TacM Syntax.Tactic := do
  `(tactic| nth_rw $(Quote.quote ((← parse smallNat) + 1)):num
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[tr_tactic nth_rewrite_lhs] def trNthRewriteLHS : TacM Syntax.Tactic := do
  `(tactic| nth_rw_lhs $(Quote.quote ((← parse smallNat) + 1))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[tr_tactic nth_rewrite_rhs] def trNthRewriteRHS : TacM Syntax.Tactic := do
  `(tactic| nth_rw_rhs $(Quote.quote ((← parse smallNat) + 1))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.pi_instances

@[tr_ni_tactic tactic.pi_instance_derive_field] def trPiInstanceDeriveField
  (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| pi_instance_derive_field)

@[tr_tactic pi_instance] def trPiInstance : TacM Syntax.Tactic := `(tactic| pi_instance)

-- # tactic.elementwise

@[tr_user_attr elementwise] def trElementwiseAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun n => do `(attr| elementwise $(← liftM $ n.mapM mkIdentI)?)

@[tr_tactic elementwise] def trElementwise : TacM Syntax.Tactic := do
  match ← parse (tk "!")?, (← parse ident*).map mkIdent with
  | none, ns => `(tactic| elementwise $[$ns]*)
  | some _, ns => `(tactic| elementwise! $[$ns]*)

@[tr_ni_tactic tactic.derive_elementwise_proof] def trDeriveElementwiseProof
  (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| derive_elementwise_proof)

-- # tactic.positivity
@[tr_tactic positivity] def trPositivity : TacM Syntax.Tactic := `(tactic| positivity)

-- # tactic.compute_degree
@[tr_tactic compute_degree_le] def trComputeDegreeLE : TacM Syntax.Tactic :=
  `(tactic| compute_degree_le)

-- # tactic.expand_exists
@[tr_user_attr expand_exists] def trExpandExists : Parse1 Syntax.Attr :=
  parse1 (ident)* fun n => do `(attr| expand_exists $[$(← liftM $ n.mapM mkIdentI)]*)

-- # tactic.move_add

@[tr_tactic move_add] def trMoveAdd : TacM Syntax.Tactic := do
  `(tactic| move_add $(← liftM $ (← parse rwRules).mapM trRwRule),* $(← trLoc (← parse location))?)

@[tr_tactic move_mul] def trMoveMul : TacM Syntax.Tactic := do
  `(tactic| move_mul $(← liftM $ (← parse rwRules).mapM trRwRule),* $(← trLoc (← parse location))?)

@[tr_tactic move_oper] def trMoveOper : TacM Syntax.Tactic := do
  let #[e] ← parse pExprList | warn! "unsupported: move_oper with multiple ops"
  `(tactic| move_op $(← trExpr e)
    $(← liftM $ (← parse rwRules).mapM trRwRule),* $(← trLoc (← parse location))?)

-- # tactic.print_sorry
@[tr_user_cmd «#print_sorry_in»] def trPrintSorryIn : Parse1 Syntax.Command :=
  parse1 ident fun n => do `(command| #print_sorry_in $(← mkIdentI n))

-- # tactic.assert_exists

@[tr_user_cmd «assert_exists»] def trAssertExists : Parse1 Syntax.Command :=
  parse1 ident fun n => do `(command| assert_exists $(← mkIdentI n))

@[tr_user_cmd «assert_not_exists»] def trAssertNotExists : Parse1 Syntax.Command :=
  parse1 ident fun n => do `(command| assert_not_exists $(← mkIdentI n))

@[tr_user_cmd «assert_instance»] def trAssertInstance : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do `(command| assert_instance $(← trExpr e))

@[tr_user_cmd «assert_no_instance»] def trAssertNoInstance : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do `(command| assert_no_instance $(← trExpr e))

-- # algebra.group.defs
attribute [tr_ni_tactic try_refl_tac] trControlLawsTac

-- # algebra.group.to_additive
@[tr_user_attr to_additive_ignore_args] def trToAdditiveIgnoreArgsAttr : Parse1 Syntax.Attr :=
  parse1 smallNat* fun n => `(attr| to_additive_ignore_args $(n.map Quote.quote)*)

@[tr_user_attr to_additive_relevant_arg] def trToAdditiveRelevantArgAttr : Parse1 Syntax.Attr :=
  parse1 smallNat fun n => `(attr| to_additive_relevant_arg $(Quote.quote n))

@[tr_user_attr to_additive_reorder] def trToAdditiveReorderAttr : Parse1 Syntax.Attr :=
  parse1 smallNat* fun n => `(attr| to_additive_reorder $(n.map Quote.quote)*)

@[tr_user_attr to_additive] def trToAdditiveAttr : Parse1 Syntax.Attr :=
  parse1 (return (optTk (← (tk "!")?).isSome, optTk (← (tk "?")?).isSome, ← (ident)?, ← (pExpr)?))
  fun (bang, ques, tgt, doc) => do
    let tgt ← liftM $ tgt.mapM mkIdentI
    let doc : Option (TSyntax strLitKind) ← doc.mapM fun doc => match doc.unparen with
    | ⟨m, Expr.string s⟩ => pure ⟨setInfo m $ Syntax.mkStrLit s⟩
    | _ => warn! "to_additive: weird doc string"
    `(attr| to_additive $[!%$bang]? $[?%$ques]? $[$tgt:ident]? $[$doc:str]?)

-- # meta.coinductive_predicates
@[tr_user_attr monotonicity] def trMonotonicityAttr := tagAttr `monotonicity

@[tr_user_cmd «coinductive»] def trCoinductivePredicate (_mods : Modifiers) :
    Parse1 Syntax.Command :=
  parse0 warn! "unsupported user cmd coinductive" -- unattested

-- # testing.slim_check.sampleable
@[tr_user_cmd «#sample»] def trSampleCmd : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do `(command| #sample $(← trExpr e))

@[tr_ni_tactic sampleable.mk_trivial_interp] def trMkTrivialInterp
  (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| refine id)

-- # testing.slim_check.testable
@[tr_ni_tactic testable.mk_decorations] def trMkDecorations
  (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| mk_decorations)

-- # logic.nontrivial
@[tr_tactic nontriviality] def trNontriviality : TacM Syntax.Tactic := do
  let t ← liftM $ (← parse (pExpr)?).mapM trExpr
  let lems := (← trSimpArgs (← parse (tk "using" *> simpArgList <|> pure #[]))).asNonempty
  `(tactic| nontriviality $[$t]? $[using $lems,*]?)

-- # order.filter.basic
@[tr_tactic filter_upwards] def trFilterUpwards : TacM Syntax.Tactic := do
  let s := (← (← parse pExprList).mapM (trExpr ·)).asNonempty
  let wth := (← parse withIdentList).map trIdent_ |>.asNonempty
  let tgt ← (← parse (tk "using" *> pExpr)?).mapM (trExpr ·)
  `(tactic| filter_upwards $[[$s:term,*]]? $[with $[$wth:term]*]? $[using $tgt:term]?)

-- # order.liminf_limsup
@[tr_ni_tactic isBounded_default] def trIsBounded_default (_ : AST3.Expr) : M Syntax.Tactic := do
  `(tactic| isBounded_default)

-- # data.opposite
@[tr_tactic op_induction] def trOpInduction : TacM Syntax.Tactic := do
  `(tactic| op_induction $[$((← parse (ident)?).map mkIdent):ident]?)

-- # data.qpf.multivariate.constructions.cofix
@[tr_tactic mv_bisim] def trMvBisim : TacM Syntax.Tactic := do
  `(tactic| mv_bisim
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?
    $[with $(((← parse withIdentList).map trBinderIdent).asNonempty)*]?)

-- # topology.tactic

@[tr_user_attr continuity] def trContinuityAttr := tagAttr `continuity

@[tr_tactic continuity] def trContinuity : TacM Syntax.Tactic := do
  let bang ← parse (tk "!")?; let ques ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang, ques with
  | none, none => `(tactic| continuity $[(config := $cfg)]?)
  | some _, none => `(tactic| continuity! $[(config := $cfg)]?)
  | none, some _ => `(tactic| continuity? $[(config := $cfg)]?)
  | some _, some _ => `(tactic| continuity!? $[(config := $cfg)]?)

@[tr_tactic continuity'] def trContinuity' : TacM Syntax.Tactic := `(tactic| continuity)
@[tr_ni_tactic tactic.interactive.continuity'] def trNIContinuity'
  (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| continuity)

-- # topology.unit_interval
@[tr_tactic unit_interval] def trUnitInterval : TacM Syntax.Tactic := `(tactic| unit_interval)

-- # data.equiv.local_equiv
@[tr_tactic mfld_set_tac] def trMfldSetTac : TacM Syntax.Tactic := `(tactic| mfld_set_tac)

-- # measure_theory.constructions.borel_space
@[tr_tactic borelize] def trBorelize : TacM Syntax.Tactic := do
  `(tactic| borelize $[$(← liftM $ (← parse pExprListOrTExpr).mapM trExpr):term]*)

-- # measure_theory.measure.measure_space_def
@[tr_ni_tactic volume_tac] def trVolumeTac (_ : AST3.Expr) : M Syntax.Tactic := do
  `(tactic| exact $(← mkIdentI `measure_theory.measure_space.volume))

-- # measure_theory.tactic

@[tr_user_attr measurability] def trMeasurabilityAttr := tagAttr `measurability

@[tr_tactic measurability] def trMeasurability : TacM Syntax.Tactic := do
  let bang ← parse (tk "!")?; let ques ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang, ques with
  | none, none => `(tactic| measurability $[(config := $cfg)]?)
  | some _, none => `(tactic| measurability! $[(config := $cfg)]?)
  | none, some _ => `(tactic| measurability? $[(config := $cfg)]?)
  | some _, some _ => `(tactic| measurability!? $[(config := $cfg)]?)

@[tr_tactic measurability'] def trMeasurability' : TacM Syntax.Tactic := `(tactic| measurability)

-- # measure_theory.integral.interval_integral
@[tr_ni_tactic unique_diff_within_at_Ici_Iic_univ]
def trUniqueDiffWithinAt_Ici_Iic_univ (_ : AST3.Expr) : M Syntax.Tactic := do
  `(tactic| uniqueDiffWithinAt_Ici_Iic_univ)

-- # category_theory.monoidal.coherence
@[tr_tactic coherence] def trCoherence : TacM Syntax.Tactic := `(tactic| coherence)
@[tr_tactic pure_coherence] def trPureCoherence : TacM Syntax.Tactic := `(tactic| pure_coherence)

-- # set_theory.game.pgame
@[tr_ni_tactic pgame.pgame_wf_tac] def trPGameWFTac (_ : AST3.Expr) : M Syntax.Tactic :=
  `(tactic| pgame_wf_tac)
