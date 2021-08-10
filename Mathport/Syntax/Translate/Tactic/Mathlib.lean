/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

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

@[trTactic rcases] def trRCases : TacM Syntax := do
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

@[trTactic obtain] def trObtain : TacM Syntax := do
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

@[trTactic rintro rintros] def trRIntro : TacM Syntax := do
  liftM $ match ← parse rintroArg with
  | Sum.inr depth => `(tactic| rintro? $[: $(depth.map fun n => Syntax.mkNumLit (toString n))]?)
  | Sum.inl (pats, ty) => show M _ from do
    `(tactic| rintro $[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?)

@[trTactic exactI] def trExactI : TacM Syntax := do
  throw! "unsupported tactic exactI"
@[trTactic resetI] def trResetI : TacM Syntax := do
  throw! "unsupported tactic resetI"
@[trTactic haveI] def trHaveI : TacM Syntax := do
  throw! "unsupported tactic haveI"
@[trTactic ext1] def trExt1 : TacM Syntax := do
  throw! "unsupported tactic ext1"
@[trTactic ext] def trExt : TacM Syntax := do
  throw! "unsupported tactic ext"
@[trTactic simpa] def trSimpa : TacM Syntax := do
  throw! "unsupported tactic simpa"
@[trTactic simp_rw] def trSimpRw : TacM Syntax := do
  throw! "unsupported tactic simp_rw"
@[trTactic use] def trUse : TacM Syntax := do
  throw! "unsupported tactic use"
@[trTactic fsplit] def trFsplit : TacM Syntax := do
  throw! "unsupported tactic fsplit"
@[trTactic casesI] def trCasesI : TacM Syntax := do
  throw! "unsupported tactic casesI"
@[trTactic swap] def trSwap : TacM Syntax := do
  throw! "unsupported tactic swap"
@[trTactic classical] def trClassical : TacM Syntax := do
  throw! "unsupported tactic classical"
@[trTactic contrapose] def trContrapose : TacM Syntax := do
  throw! "unsupported tactic contrapose"
@[trTactic introsI] def trIntrosI : TacM Syntax := do
  throw! "unsupported tactic introsI"
@[trTactic push_neg] def trPushNeg : TacM Syntax := do
  throw! "unsupported tactic push_neg"
@[trTactic inhabit] def trInhabit : TacM Syntax := do
  throw! "unsupported tactic inhabit"
@[trTactic replace] def trReplace : TacM Syntax := do
  throw! "unsupported tactic replace"
@[trTactic congr'] def trCongr' : TacM Syntax := do
  throw! "unsupported tactic congr'"
@[trTactic clear_except] def trClearExcept : TacM Syntax := do
  throw! "unsupported tactic clear_except"
@[trTactic letI] def trLetI : TacM Syntax := do
  throw! "unsupported tactic letI"
@[trTactic tauto] def trTauto : TacM Syntax := do
  throw! "unsupported tactic tauto"
@[trTactic refine_struct] def trRefineStruct : TacM Syntax := do
  throw! "unsupported tactic refine_struct"
@[trTactic unfreezingI] def trUnfreezingI : TacM Syntax := do
  throw! "unsupported tactic unfreezingI"
@[trTactic assoc_rw] def trAssocRw : TacM Syntax := do
  throw! "unsupported tactic assoc_rw"
@[trTactic conv_rhs] def trConvRhs : TacM Syntax := do
  throw! "unsupported tactic conv_rhs"
@[trTactic conv_lhs] def trConvLhs : TacM Syntax := do
  throw! "unsupported tactic conv_lhs"
@[trTactic pi_instance] def trPiInstance : TacM Syntax := do
  throw! "unsupported tactic pi_instance"
@[trTactic split_ifs] def trSplitIfs : TacM Syntax := do
  throw! "unsupported tactic split_ifs"
@[trTactic safe] def trSafe : TacM Syntax := do
  throw! "unsupported tactic safe"
@[trTactic finish] def trFinish : TacM Syntax := do
  throw! "unsupported tactic finish"
@[trTactic convert] def trConvert : TacM Syntax := do
  throw! "unsupported tactic convert"
@[trTactic choose] def trChoose : TacM Syntax := do
  throw! "unsupported tactic choose"
@[trTactic substs] def trSubsts : TacM Syntax := do
  throw! "unsupported tactic substs"
@[trTactic mfld_set_tac] def trMfldSetTac : TacM Syntax := do
  throw! "unsupported tactic mfld_set_tac"
@[trTactic introI] def trIntroI : TacM Syntax := do
  throw! "unsupported tactic introI"
@[trTactic tidy] def trTidy : TacM Syntax := do
  throw! "unsupported tactic tidy"
@[trTactic push_cast] def trPushCast : TacM Syntax := do
  throw! "unsupported tactic push_cast"
@[trTactic lift] def trLift : TacM Syntax := do
  throw! "unsupported tactic lift"
@[trTactic norm_cast] def trNormCast : TacM Syntax := do
  throw! "unsupported tactic norm_cast"
@[trTactic solve_by_elim] def trSolveByElim : TacM Syntax := do
  throw! "unsupported tactic solve_by_elim"
@[trTactic nontriviality] def trNontriviality : TacM Syntax := do
  throw! "unsupported tactic nontriviality"
@[trTactic set] def trSet : TacM Syntax := do
  throw! "unsupported tactic set"
@[trTactic exact_mod_cast] def trExactModCast : TacM Syntax := do
  throw! "unsupported tactic exact_mod_cast"
@[trTactic clean] def trClean : TacM Syntax := do
  throw! "unsupported tactic clean"
@[trTactic substI] def trSubstI : TacM Syntax := do
  throw! "unsupported tactic substI"
@[trTactic clear_aux_decl] def trClearAuxDecl : TacM Syntax := do
  throw! "unsupported tactic clear_aux_decl"
@[trTactic unfold_wf] def trUnfoldWf : TacM Syntax := do
  throw! "unsupported tactic unfold_wf"
@[trTactic generalize_hyp] def trGeneralizeHyp : TacM Syntax := do
  throw! "unsupported tactic generalize_hyp"
@[trTactic unfold_coes] def trUnfoldCoes : TacM Syntax := do
  throw! "unsupported tactic unfold_coes"
@[trTactic clear_] def trClear_ : TacM Syntax := do
  throw! "unsupported tactic clear_"
@[trTactic wlog] def trWlog : TacM Syntax := do
  throw! "unsupported tactic wlog"
@[trTactic mono] def trMono : TacM Syntax := do
  throw! "unsupported tactic mono"
@[trTactic convert_to] def trConvertTo : TacM Syntax := do
  throw! "unsupported tactic convert_to"
@[trTactic transitivity'] def trTransitivity' : TacM Syntax := do
  throw! "unsupported tactic transitivity'"
@[trTactic apply'] def trApply' : TacM Syntax := do
  throw! "unsupported tactic apply'"
@[trTactic refl'] def trRefl' : TacM Syntax := do
  throw! "unsupported tactic refl'"
@[trTactic nth_rewrite] def trNthRewrite : TacM Syntax := do
  throw! "unsupported tactic nth_rewrite"
@[trTactic rcongr] def trRcongr : TacM Syntax := do
  throw! "unsupported tactic rcongr"
@[trTactic dec_trivial] def trDecTrivial : TacM Syntax := do
  throw! "unsupported tactic dec_trivial"
@[trTactic slice_lhs] def trSliceLhs : TacM Syntax := do
  throw! "unsupported tactic slice_lhs"
@[trTactic apply_rules] def trApplyRules : TacM Syntax := do
  throw! "unsupported tactic apply_rules"
@[trTactic norm_num] def trNormNum : TacM Syntax := do
  throw! "unsupported tactic norm_num"
@[trTactic apply_normed] def trApplyNormed : TacM Syntax := do
  throw! "unsupported tactic apply_normed"
@[trTactic apply_mod_cast] def trApplyModCast : TacM Syntax := do
  throw! "unsupported tactic apply_mod_cast"
@[trTactic ring] def trRing : TacM Syntax := do
  throw! "unsupported tactic ring"
@[trTactic abel] def trAbel : TacM Syntax := do
  throw! "unsupported tactic abel"
@[trTactic trunc_cases] def trTruncCases : TacM Syntax := do
  throw! "unsupported tactic trunc_cases"
@[trTactic unfold_aux] def trUnfoldAux : TacM Syntax := do
  throw! "unsupported tactic unfold_aux"
@[trTactic triv] def trTriv : TacM Syntax := do
  throw! "unsupported tactic triv"
@[trTactic mv_bisim] def trMvBisim : TacM Syntax := do
  throw! "unsupported tactic mv_bisim"
@[trTactic ring_nf] def trRingNf : TacM Syntax := do
  throw! "unsupported tactic ring_nf"
@[trTactic rw_mod_cast] def trRwModCast : TacM Syntax := do
  throw! "unsupported tactic rw_mod_cast"
@[trTactic linarith] def trLinarith : TacM Syntax := do
  throw! "unsupported tactic linarith"
@[trTactic apply_fun] def trApplyFun : TacM Syntax := do
  throw! "unsupported tactic apply_fun"
@[trTactic field_simp] def trFieldSimp : TacM Syntax := do
  throw! "unsupported tactic field_simp"
@[trTactic slice_rhs] def trSliceRhs : TacM Syntax := do
  throw! "unsupported tactic slice_rhs"
@[trTactic match_hyp] def trMatchHyp : TacM Syntax := do
  throw! "unsupported tactic match_hyp"
@[trTactic interval_cases] def trIntervalCases : TacM Syntax := do
  throw! "unsupported tactic interval_cases"
@[trTactic nth_rewrite_rhs] def trNthRewriteRhs : TacM Syntax := do
  throw! "unsupported tactic nth_rewrite_rhs"
@[trTactic equiv_rw] def trEquivRw : TacM Syntax := do
  throw! "unsupported tactic equiv_rw"
@[trTactic group] def trGroup : TacM Syntax := do
  throw! "unsupported tactic group"
@[trTactic tfae_have] def trTfaeHave : TacM Syntax := do
  throw! "unsupported tactic tfae_have"
@[trTactic id] def trId : TacM Syntax := do
  throw! "unsupported tactic id"
@[trTactic filter_upwards] def trFilterUpwards : TacM Syntax := do
  throw! "unsupported tactic filter_upwards"
@[trTactic assumption_mod_cast] def trAssumptionModCast : TacM Syntax := do
  throw! "unsupported tactic assumption_mod_cast"
@[trTactic continuity] def trContinuity : TacM Syntax := do
  throw! "unsupported tactic continuity"
@[trTactic work_on_goal] def trWorkOnGoal : TacM Syntax := do
  throw! "unsupported tactic work_on_goal"
@[trTactic generalize_proofs] def trGeneralizeProofs : TacM Syntax := do
  throw! "unsupported tactic generalize_proofs"
@[trTactic fin_cases] def trFinCases : TacM Syntax := do
  throw! "unsupported tactic fin_cases"
@[trTactic symmetry'] def trSymmetry' : TacM Syntax := do
  throw! "unsupported tactic symmetry'"
@[trTactic op_induction] def trOpInduction : TacM Syntax := do
  throw! "unsupported tactic op_induction"
@[trTactic clear_value] def trClearValue : TacM Syntax := do
  throw! "unsupported tactic clear_value"
@[trTactic ring_exp] def trRingExp : TacM Syntax := do
  throw! "unsupported tactic ring_exp"
@[trTactic noncomm_ring] def trNoncommRing : TacM Syntax := do
  throw! "unsupported tactic noncomm_ring"
@[trTactic generalize'] def trGeneralize' : TacM Syntax := do
  throw! "unsupported tactic generalize'"
@[trTactic fconstructor] def trFconstructor : TacM Syntax := do
  throw! "unsupported tactic fconstructor"
@[trTactic padic_index_simp] def trPadicIndexSimp : TacM Syntax := do
  throw! "unsupported tactic padic_index_simp"
@[trTactic rotate] def trRotate : TacM Syntax := do
  throw! "unsupported tactic rotate"
@[trTactic nlinarith] def trNlinarith : TacM Syntax := do
  throw! "unsupported tactic nlinarith"
@[trTactic unit_interval] def trUnitInterval : TacM Syntax := do
  throw! "unsupported tactic unit_interval"
@[trTactic ghost_fun_tac] def trGhostFunTac : TacM Syntax := do
  throw! "unsupported tactic ghost_fun_tac"
@[trTactic ghost_calc] def trGhostCalc : TacM Syntax := do
  throw! "unsupported tactic ghost_calc"
@[trTactic init_ring] def trInitRing : TacM Syntax := do
  throw! "unsupported tactic init_ring"
@[trTactic ghost_simp] def trGhostSimp : TacM Syntax := do
  throw! "unsupported tactic ghost_simp"
@[trTactic witt_truncate_fun_tac] def trWittTruncateFunTac : TacM Syntax := do
  throw! "unsupported tactic witt_truncate_fun_tac"
@[trTactic apply_assumption] def trApplyAssumption : TacM Syntax := do
  throw! "unsupported tactic apply_assumption"
@[trTactic cancel_denoms] def trCancelDenoms : TacM Syntax := do
  throw! "unsupported tactic cancel_denoms"
@[trTactic norm_num1] def trNormNum1 : TacM Syntax := do
  throw! "unsupported tactic norm_num1"
@[trTactic clear_dependent] def trClearDependent : TacM Syntax := do
  throw! "unsupported tactic clear_dependent"

@[trUserAttr functor_norm] def trFunctorNorm : TacM Syntax := do
  throw! "unsupported user attr functor_norm"
@[trUserAttr higher_order] def trHigherOrder : TacM Syntax := do
  throw! "unsupported user attr higher_order"
@[trUserAttr monotonicity] def trMonotonicity : TacM Syntax := do
  throw! "unsupported user attr monotonicity"
@[trUserAttr linter] def trLinter : TacM Syntax := do
  throw! "unsupported user attr linter"
@[trUserAttr nolint] def trNolint : TacM Syntax := do
  throw! "unsupported user attr nolint"
@[trUserAttr protect_proj] def trProtectProj : TacM Syntax := do
  throw! "unsupported user attr protect_proj"
@[trUserAttr to_additive] def trToAdditive : TacM Syntax := do
  throw! "unsupported user attr to_additive"
@[trUserAttr to_additive_ignore_args] def trToAdditiveIgnoreArgs : TacM Syntax := do
  throw! "unsupported user attr to_additive_ignore_args"
@[trUserAttr ext] def trExtAttr : TacM Syntax := do
  throw! "unsupported user attr ext"
@[trUserAttr notation_class] def trNotationClass : TacM Syntax := do
  throw! "unsupported user attr notation_class"
@[trUserAttr simps] def trSimps : TacM Syntax := do
  throw! "unsupported user attr simps"
@[trUserAttr hint_tactic] def trHintTactic : TacM Syntax := do
  throw! "unsupported user attr hint_tactic"
@[trUserAttr split_if_reduction] def trSplitIfReduction : TacM Syntax := do
  throw! "unsupported user attr split_if_reduction"
@[trUserAttr norm_cast] def trNormCastAttr : TacM Syntax := do
  throw! "unsupported user attr norm_cast"
@[trUserAttr obviously] def trObviously : TacM Syntax := do
  throw! "unsupported user attr obviously"
@[trUserAttr mk_iff] def trMkIff : TacM Syntax := do
  throw! "unsupported user attr mk_iff"
@[trUserAttr typevec] def trTypevec : TacM Syntax := do
  throw! "unsupported user attr typevec"
@[trUserAttr ancestor] def trAncestor : TacM Syntax := do
  throw! "unsupported user attr ancestor"
@[trUserAttr mono] def trMonoAttr : TacM Syntax := do
  throw! "unsupported user attr mono"
@[trUserAttr to_additive_reorder] def trToAdditiveReorder : TacM Syntax := do
  throw! "unsupported user attr to_additive_reorder"
@[trUserAttr zify] def trZify : TacM Syntax := do
  throw! "unsupported user attr zify"
@[trUserAttr reassoc] def trReassoc : TacM Syntax := do
  throw! "unsupported user attr reassoc"
@[trUserAttr norm_num] def trNormNumAttr : TacM Syntax := do
  throw! "unsupported user attr norm_num"
@[trUserAttr sugar] def trSugar : TacM Syntax := do
  throw! "unsupported user attr sugar"
@[trUserAttr sugar_nat] def trSugarNat : TacM Syntax := do
  throw! "unsupported user attr sugar_nat"
@[trUserAttr «protected»] def trProtected : TacM Syntax := do
  throw! "unsupported user attr protected"
@[trUserAttr continuity] def trContinuityAttr : TacM Syntax := do
  throw! "unsupported user attr continuity"
@[trUserAttr tidy] def trTidyAttr : TacM Syntax := do
  throw! "unsupported user attr tidy"
@[trUserAttr elementwise] def trElementwise : TacM Syntax := do
  throw! "unsupported user attr elementwise"
@[trUserAttr measurability] def trMeasurability : TacM Syntax := do
  throw! "unsupported user attr measurability"
@[trUserAttr is_poly] def trIsPoly : TacM Syntax := do
  throw! "unsupported user attr is_poly"

@[trUserCmd add_tactic_doc] def trAddTacticDoc (doc : Option String) : TacM Syntax := do
  throw! "unsupported user command add_tactic_doc"
@[trUserCmd library_note] def trLibraryNote (doc : Option String) : TacM Syntax := do
  throw! "unsupported user command library_note"
@[trUserCmd add_decl_doc] def trAddDeclDoc (doc : Option String) : TacM Syntax := do
  throw! "unsupported user command add_decl_doc"
@[trUserCmd setup_tactic_parser] def trSetupTacticParser : TacM Syntax := do
  throw! "unsupported user command setup_tactic_parser"
@[trUserCmd localized] def trLocalized : TacM Syntax := do
  throw! "unsupported user command localized"
@[trUserCmd copy_doc_string] def trCopyDocString (doc : Option String) : TacM Syntax := do
  throw! "unsupported user command copy_doc_string"
@[trUserCmd alias] def trAlias (doc : Option String) : TacM Syntax := do
  throw! "unsupported user command alias"
@[trUserCmd initialize_simps_projections] def trInitializeSimpsProjections : TacM Syntax := do
  throw! "unsupported user command initialize_simps_projections"
@[trUserCmd add_hint_tactic] def trAddHintTactic : TacM Syntax := do
  throw! "unsupported user command add_hint_tactic"
@[trUserCmd mk_simp_attribute] def trMkSimpAttribute : TacM Syntax := do
  throw! "unsupported user command mk_simp_attribute"
@[trUserCmd def_replacer] def trDefReplacer : TacM Syntax := do
  throw! "unsupported user command def_replacer"
@[trUserCmd open_locale] def trOpenLocale : TacM Syntax := do
  throw! "unsupported user command open_locale"
@[trUserCmd restate_axiom] def trRestateAxiom : TacM Syntax := do
  throw! "unsupported user command restate_axiom"
@[trUserCmd mk_iff_of_inductive_prop] def trMkIffOfInductiveProp : TacM Syntax := do
  throw! "unsupported user command mk_iff_of_inductive_prop"

def trInterpolatedStr' := trInterpolatedStr fun stx => `(← $stx)
@[trUserNota tactic.pformat_macro] def trPFormatMacro : TacM Syntax := do
  `(f! $(← trInterpolatedStr'))
@[trUserNota tactic.fail_macro] def trFailMacro : TacM Syntax := do
  `(throwError $(← trInterpolatedStr'))
@[trUserNota tactic.trace_macro] def trTraceMacro : TacM Syntax := do
  let stx ← trInterpolatedStr'; `(← do dbg_trace $stx)