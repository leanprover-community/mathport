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
open AST3 Parser

-- # tactic.trunc_cases
@[trTactic trunc_cases] def trTruncCases : TacM Syntax := do
  `(tactic| trunc_cases $(← trExpr (← parse pExpr))
    $[with $(((← parse withIdentList).map trBinderIdent).asNonempty)*]?)

-- # tactic.abel
@[trTactic abel1] def trAbel1 : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| abel1)
  | some _ => `(tactic| abel1!)

@[trTactic abel] def trAbel : TacM Syntax := do
  match ← parse (tk "!")?, ← parse (ident)?, ← trLoc (← parse location) with
  | none, none, loc => `(tactic| abel $(loc)?)
  | none, some `raw, loc => `(tactic| abel raw $(loc)?)
  | none, some `term, loc => `(tactic| abel term $(loc)?)
  | some _, none, loc => `(tactic| abel! $(loc)?)
  | some _, some `raw, loc => `(tactic| abel! raw $(loc)?)
  | some _, some `term, loc => `(tactic| abel! term $(loc)?)
  | _, _, _ => warn! "bad abel mode"

-- # tactic.linear_combination
@[trTactic linear_combination] def trLinearCombination : TacM Syntax := do
  let es ← parse (
    (return (← tk "(" *> ident, some $ ← tk "," *> pExpr <* tk ")")) <|>
    (return (← ident, none)))*
  let es ← es.mapM fun
  | (x, none) => pure $ mkIdent x
  | (x, some n) => return mkNode ``Parser.Tactic.nameAndTerm #[mkIdent x, mkAtom "*", ← trExpr n]
  pure $ mkNode ``Parser.Tactic.linearCombination #[mkAtom "linear_combination",
    ← mkConfigStx (← liftM $ (← expr?).mapM trExpr), Syntax.mkSep es (mkAtom "+")]

-- # tactic.noncomm_ring
@[trTactic noncomm_ring] def trNoncommRing : TacM Syntax := `(tactic| noncomm_ring)

-- # tactic.omega
@[trTactic omega] def trOmega : TacM Syntax := do
  let args ← parse ident*
  pure $ mkNode ``Parser.Tactic.omega #[mkAtom "omega",
    mkNullNode $ if args.contains `manual then #[mkAtom "manual"] else #[],
    mkNullNode $
      if args.contains `int then #[mkAtom "int"] else
      if args.contains `nat then #[mkAtom "nat"] else #[]]

-- # tactic.fin_cases
@[trTactic fin_cases] def trFinCases : TacM Syntax := do
  let hyp ← parse $ (tk "*" *> pure none) <|> (some <$> ident)
  let w ← liftM $ (← parse (tk "with" *> pExpr)?).mapM trExpr
  match hyp with
  | none => `(tactic| fin_cases * $[with $w]?)
  | some h => `(tactic| fin_cases $(mkIdent h):ident $[with $w]?)

-- # tactic.interval_cases
@[trTactic interval_cases] def trIntervalCases : TacM Syntax :=
  return mkNode ``Parser.Tactic.intervalCases #[mkAtom "interval_cases",
    ← mkOpt (← parse (pExpr)?) trExpr,
    ← mkOptionalNodeM (← parse (tk "using" *> return (← ident, ← ident))?) fun (x, y) =>
      return #[mkAtom "using", mkIdent x, mkAtom ",", mkIdent y],
    mkOptionalNode' (← parse (tk "with" *> ident)?) fun h => #[mkAtom "with", mkIdent h]]

-- # tactic.subtype_instance
@[trTactic subtype_instance] def trSubtypeInstance : TacM Syntax := `(tactic| subtype_instance)

-- # tactic.derive_fintype

-- # tactic.group
@[trTactic group] def trGroup : TacM Syntax := do
  `(tactic| group $(← trLoc (← parse location))?)

-- # tactic.cancel_denoms
@[trTactic cancel_denoms] def trCancelDenoms : TacM Syntax := do
  `(tactic| cancel_denoms $(← trLoc (← parse location))?)

-- # tactic.transport
@[trTactic transport] def trTransport : TacM Syntax := do
  `(tactic| transport
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?
    using $(← trExpr (← parse (tk "using" *> pExpr))))

-- # tactic.unfold_cases
@[trTactic unfold_cases] def trUnfoldCases : TacM Syntax := do
  `(tactic| unfold_cases $(← trBlock (← itactic)):tacticSeq)

-- # tactic.field_simp
@[trTactic field_simp] def trFieldSimp : TacM Syntax := do
  let o := optTk (← parse onlyFlag)
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let loc ← trLoc (← parse location)
  let (cfg, disch) ← parseSimpConfig (← expr?)
  let cfg ← mkConfigStx? $ cfg.bind quoteSimpConfig
  `(tactic| field_simp $(cfg)? $(disch)? $[only%$o]? $[[$hs,*]]? $[with $attrs*]? $(loc)?)

-- # tactic.equiv_rw

@[trTactic equiv_rw] def trEquivRw : TacM Syntax := do
  let es ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  let loc ← trLoc (← parse location)
  let cfg ← liftM $ (← expr?).mapM trExpr
  match es with
  | #[e] => `(tactic| equiv_rw $[(config := $cfg)]? $e $[$loc]?)
  | _ => `(tactic| equiv_rw $[(config := $cfg)]? [$es,*] $[$loc]?)

@[trTactic equiv_rw_type] def trEquivRwType : TacM Syntax := do
  let e ← trExpr (← parse pExpr)
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| equiv_rw_type $[(config := $cfg)]? $e)

-- # tactic.nth_rewrite

@[trTactic nth_rewrite] def trNthRewrite : TacM Syntax := do
  `(tactic| nth_rw $(Quote.quote (← parse smallNat))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[trTactic nth_rewrite_lhs] def trNthRewriteLHS : TacM Syntax := do
  `(tactic| nth_rw_lhs $(Quote.quote (← parse smallNat))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

@[trTactic nth_rewrite_rhs] def trNthRewriteRHS : TacM Syntax := do
  `(tactic| nth_rw_rhs $(Quote.quote (← parse smallNat))
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.pi_instances

@[trNITactic tactic.pi_instance_derive_field] def trPiInstanceDeriveField
  (_ : AST3.Expr) : M Syntax := `(tactic| pi_instance_derive_field)

@[trTactic pi_instance] def trPiInstance : TacM Syntax := `(tactic| pi_instance)

-- # tactic.elementwise

@[trUserAttr elementwise] def trElementwiseAttr : TacM Syntax := do
  `(attr| elementwise $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trTactic elementwise] def trElementwise : TacM Syntax := do
  match ← parse (tk "!")?, (← parse ident*).map mkIdent with
  | none, ns => `(tactic| elementwise $ns*)
  | some _, ns => `(tactic| elementwise! $ns*)

@[trNITactic tactic.derive_elementwise_proof] def trDeriveElementwiseProof
  (_ : AST3.Expr) : M Syntax := `(tactic| derive_elementwise_proof)

-- # algebra.group.defs
attribute [trNITactic try_refl_tac] trControlLawsTac

-- # algebra.group.to_additive
@[trUserAttr to_additive_ignore_args] def trToAdditiveIgnoreArgsAttr : TacM Syntax := do
  `(attr| to_additive_ignore_args $((← parse smallNat*).map Quote.quote)*)

@[trUserAttr to_additive_relevant_arg] def trToAdditiveRelevantArgAttr : TacM Syntax := do
  `(attr| to_additive_relevant_arg $(Quote.quote (← parse smallNat)))

@[trUserAttr to_additive_reorder] def trToAdditiveReorderAttr : TacM Syntax := do
  `(attr| to_additive_reorder $((← parse smallNat*).map Quote.quote)*)

@[trUserAttr to_additive] def trToAdditiveAttr : TacM Syntax := do
  let (bang, ques, tgt, doc) ← parse <|
    return (optTk (← (tk "!")?).isSome, optTk (← (tk "?")?).isSome, ← (ident)?, ← (pExpr)?)
  let tgt ← liftM $ tgt.mapM mkIdentI
  let doc ← doc.mapM fun doc => match doc.unparen with
  | ⟨m, Expr.string s⟩ => pure $ setInfo m $ Syntax.mkStrLit s
  | _ => warn! "to_additive: weird doc string"
  `(attr| to_additive $[!%$bang]? $[?%$ques]? $[$tgt:ident]? $[$doc:str]?)

-- # meta.coinductive_predicates
@[trUserAttr monotonicity] def trMonotonicityAttr := tagAttr `monotonicity

@[trUserCmd «coinductive»] def trCoinductivePredicate (mods : Modifiers) : TacM Syntax :=
  parse_0 warn! "unsupported user cmd coinductive" -- unattested

-- # testing.slim_check.sampleable
@[trUserCmd «#sample»] def trSampleCmd : TacM Syntax := do
  `(command| #sample $(← trExpr (← parse pExpr)))

@[trNITactic sampleable.mk_trivial_interp] def trMkTrivialInterp
  (_ : AST3.Expr) : M Syntax := `(tactic| refine id)

-- # testing.slim_check.testable
@[trNITactic testable.mk_decorations] def trMkDecorations
  (_ : AST3.Expr) : M Syntax := `(tactic| mk_decorations)

-- # logic.nontrivial
@[trTactic nontriviality] def trNontriviality : TacM Syntax := do
  let t ← liftM $ (← parse (pExpr)?).mapM trExpr
  let lems := (← trSimpArgs (← parse (tk "using" *> simpArgList <|> pure #[]))).asNonempty
  `(tactic| nontriviality $[$t]? $[using $lems,*]?)

-- # order.filter.basic
@[trTactic filter_upwards] def trFilterUpwards : TacM Syntax := do
  let s := (← (← parse pExprList).mapM (trExpr ·)).asNonempty
  let wth := (← parse withIdentList).map trBinderIdent |>.asNonempty
  let tgt ← (← parse (tk "using" *> pExpr)?).mapM (trExpr ·)
  `(tactic| filter_upwards $[[$s:term,*]]? $[with $[$wth:term]*]? $[using $tgt:term]?)

-- # order.liminf_limsup
@[trNITactic isBounded_default] def trIsBounded_default (_ : AST3.Expr) : M Syntax := do
  `(tactic| isBounded_default)

-- # data.opposite
@[trTactic op_induction] def trOpInduction : TacM Syntax := do
  `(tactic| op_induction $[$((← parse (ident)?).map mkIdent):ident]?)

-- # data.qpf.multivariate.constructions.cofix
@[trTactic mv_bisim] def trMvBisim : TacM Syntax := do
  `(tactic| mv_bisim
    $[$(← liftM $ (← parse (pExpr)?).mapM trExpr)]?
    $[with $(((← parse withIdentList).map trBinderIdent).asNonempty)*]?)

-- # topology.tactic

@[trUserAttr continuity] def trContinuityAttr := tagAttr `continuity

@[trTactic continuity] def trContinuity : TacM Syntax := do
  let bang ← parse (tk "!")?; let ques ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang, ques with
  | none, none => `(tactic| continuity $[(config := $cfg)]?)
  | some _, none => `(tactic| continuity! $[(config := $cfg)]?)
  | none, some _ => `(tactic| continuity? $[(config := $cfg)]?)
  | some _, some _ => `(tactic| continuity!? $[(config := $cfg)]?)

@[trTactic continuity'] def trContinuity' : TacM Syntax := `(tactic| continuity)
@[trNITactic tactic.interactive.continuity'] def trNIContinuity'
  (_ : AST3.Expr) : M Syntax := `(tactic| continuity)

-- # topology.unit_interval
@[trTactic unit_interval] def trUnitInterval : TacM Syntax := `(tactic| unit_interval)

-- # data.equiv.local_equiv
@[trTactic mfld_set_tac] def trMfldSetTac : TacM Syntax := `(tactic| mfld_set_tac)

-- # measure_theory.measure.measure_space_def
@[trNITactic volume_tac] def trVolumeTac (_ : AST3.Expr) : M Syntax := do
  `(tactic| exact $(← mkIdentI `measure_theory.measure_space.volume))

-- # measure_theory.tactic

@[trUserAttr measurability] def trMeasurabilityAttr := tagAttr `measurability

@[trTactic measurability] def trMeasurability : TacM Syntax := do
  let bang ← parse (tk "!")?; let ques ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang, ques with
  | none, none => `(tactic| measurability $[(config := $cfg)]?)
  | some _, none => `(tactic| measurability! $[(config := $cfg)]?)
  | none, some _ => `(tactic| measurability? $[(config := $cfg)]?)
  | some _, some _ => `(tactic| measurability!? $[(config := $cfg)]?)

@[trTactic measurability'] def trMeasurability' : TacM Syntax := `(tactic| measurability)

-- # measure_theory.integral.interval_integral
@[trNITactic unique_diff_within_at_Ici_Iic_univ] def trUniqueDiffWithinAt_Ici_Iic_univ (_ : AST3.Expr) : M Syntax := do
  `(tactic| uniqueDiffWithinAt_Ici_Iic_univ)
