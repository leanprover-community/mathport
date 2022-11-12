/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.interactive

@[tr_tactic fconstructor] def trFConstructor : TacM Syntax.Tactic := `(tactic| fconstructor)

@[tr_tactic try_for] def trTryFor : TacM Syntax.Tactic := do
  `(tactic| try_for $(← trExpr (← parse pExpr)) $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic substs] def trSubsts : TacM Syntax.Tactic := do
  `(tactic| substs $[$((← parse ident*).map mkIdent)]*)

@[tr_tactic unfold_coes] def trUnfoldCoes : TacM Syntax.Tactic := do
  `(tactic| unfold_coes $(← trLoc (← parse location))?)

@[tr_tactic unfold_wf] def trUnfoldWf : TacM Syntax.Tactic := `(tactic| unfold_wf)

@[tr_tactic unfold_aux] def trUnfoldAux : TacM Syntax.Tactic := `(tactic| unfold_aux)

@[tr_tactic recover] def trRecover : TacM Syntax.Tactic :=
  return mkBlockTransform fun args => `(tactic| recover $args*)

@[tr_tactic «continue»] def trContinue : TacM Syntax.Tactic := do
  `(tactic| continue $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic id] def trId : TacM Syntax.Tactic := do trIdTactic (← itactic)

@[tr_tactic work_on_goal] def trWorkOnGoal : TacM Syntax.Tactic := do
  `(tactic| on_goal $(Quote.quote (← parse smallNat)) =>
    $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic swap] def trSwap : TacM Syntax.Tactic := do
  let n ← (← expr?).mapM fun
  | ⟨_, AST3.Expr.nat n⟩ => pure n
  | _ => warn! "unsupported: weird nat"
  match n.getD 2 with
  | 1 => `(tactic| skip)
  | 2 => `(tactic| swap)
  | n => `(tactic| pick_goal $(Quote.quote n))

@[tr_tactic rotate] def trRotate : TacM Syntax.Tactic := do
  let n ← (← expr?).mapM fun
  | ⟨_, AST3.Expr.nat n⟩ => pure n
  | _ => warn! "unsupported: weird nat"
  match n.getD 1 with
  | 0 => `(tactic| skip)
  | 1 => `(tactic| rotate_left)
  | n => `(tactic| rotate_left $(Quote.quote n))

@[tr_tactic clear_] def trClear_ : TacM Syntax.Tactic := `(tactic| clear_)

@[tr_tactic replace] def trReplace : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| replace $[$h]? $[: $ty]? := $(← trExpr pr))
  | none =>  `(tactic| replace $[$h]? $[: $ty]?)

@[tr_tactic classical] def trClassical : TacM Syntax.Tactic := do
  let force := (← parse (tk "!")?).isSome
  if force then `(tactic| classical!)
  else return mkBlockTransform fun args => `(tactic| classical $args*)

@[tr_tactic generalize_hyp] def trGeneralizeHyp : TacM Syntax.Tactic := do
  let h := (← parse (ident)?).map mkIdent
  parse (tk ":")
  let (e, x) ← parse generalizeArg
  `(tactic| generalize $[$h :]? $(← trExpr e) = $(mkIdent x) $(← trLoc (← parse location))?)

@[tr_tactic clean] def trClean : TacM Syntax.Tactic := do
  `(tactic| clean $(← trExpr (← parse pExpr)))

@[tr_tactic refine_struct] def trRefineStruct : TacM Syntax.Tactic := do
  `(tactic| refine_struct $(← trExpr (← parse pExpr)))

@[tr_tactic guard_hyp'] def trGuardHyp' : TacM Syntax.Tactic := do
  `(tactic| guard_hyp $(mkIdent (← parse ident)) :ₐ $(← trExpr (← parse (tk ":" *> pExpr))))

@[tr_tactic match_hyp] def trMatchHyp : TacM Syntax.Tactic := do
  let h := mkIdent (← parse ident)
  let ty ← trExpr (← parse (tk ":" *> pExpr))
  let m ← liftM $ (← expr?).mapM trExpr
  `(tactic| match_hyp $[(m := $m)]? $h : $ty)

@[tr_tactic guard_expr_strict] def trGuardExprStrict : TacM Syntax.Tactic := do
  let t ← expr!
  let p ← parse (tk ":=" *> pExpr)
  `(tactic| guard_expr $(← trExpr t):term =ₛ $(← trExpr p):term)

@[tr_tactic guard_target_strict] def trGuardTargetStrict : TacM Syntax.Tactic := do
  `(tactic| guard_target =ₛ $(← trExpr (← parse pExpr)))

@[tr_tactic guard_hyp_strict] def trGuardHypStrict : TacM Syntax.Tactic := do
  `(tactic| guard_hyp $(mkIdent (← parse ident)) :ₛ $(← trExpr (← parse (tk ":" *> pExpr))))

@[tr_tactic guard_hyp_nums] def trGuardHypNums : TacM Syntax.Tactic := do
  match (← expr!).kind.unparen with
  | AST3.Expr.nat n => `(tactic| guard_hyp_nums $(Quote.quote n))
  | _ => warn! "unsupported: weird nat"

@[tr_tactic guard_target_mod_implicit] def trGuardTargetModImplicit : TacM Syntax.Tactic := do
  `(tactic| guard_target = $(← trExpr (← parse pExpr)))

@[tr_tactic guard_hyp_mod_implicit] def trGuardHypModImplicit : TacM Syntax.Tactic := do
  `(tactic| guard_hyp $(mkIdent (← parse ident)) : $(← trExpr (← parse (tk ":" *> pExpr))))

@[tr_tactic guard_tags] def trGuardTags : TacM Syntax.Tactic := do
  `(tactic| guard_tags $[$((← parse ident*).map mkIdent)]*)

@[tr_tactic guard_proof_term] def trGuardProofTerm : TacM Syntax.Tactic := do
  `(tactic| guard_proof_term $(← trIdTactic (← itactic)) => $(← trExpr (← parse pExpr)))

@[tr_tactic success_if_fail_with_msg] def trSuccessIfFailWithMsg : TacM Syntax.Tactic := do
  let t ← trBlock (← itactic)
  match (← expr!).kind.unparen with
  | AST3.Expr.string s => `(tactic| fail_if_success? $(Syntax.mkStrLit s) $t:tacticSeq)
  | _ => warn! "unsupported: weird string"

@[tr_tactic field] def trField : TacM Syntax.Tactic := do
  `(tactic| field $(mkIdent (← parse ident)) => $(← trBlock (← itactic)):tacticSeq)

@[tr_tactic have_field] def trHaveField : TacM Syntax.Tactic := `(tactic| have_field)

@[tr_tactic apply_field] def trApplyField : TacM Syntax.Tactic := `(tactic| apply_field)

@[tr_tactic apply_rules] def trApplyRules : TacM Syntax.Tactic := do
  let hs ← liftM $ (← parse optPExprList).mapM trExpr
  let hs := hs ++ (← parse (tk "with" *> ident*)).map mkIdent
  let n ← (← expr?).mapM fun
  | ⟨_, AST3.Expr.nat n⟩ => pure $ Quote.quote n
  | _ => warn! "unsupported: weird nat"
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| apply_rules $[(config := $cfg)]? [$hs,*] $(n)?)

@[tr_tactic h_generalize] def trHGeneralize : TacM Syntax.Tactic := do
  let rev ← parse (tk "!")?
  let h := (← parse (ident_)?).map trBinderIdent
  let (e, x) ← parse (tk ":") *> parse hGeneralizeArg
  let e ← trExpr e; let x := mkIdent x
  let eqsH := (← parse (tk "with" *> ident_)?).map trBinderIdent
  match rev with
  | none => `(tactic| h_generalize $[$h :]? $e = $x $[with $eqsH]?)
  | some _ => `(tactic| h_generalize! $[$h :]? $e = $x $[with $eqsH]?)

@[tr_tactic guard_expr_eq'] def trGuardExprEq' : TacM Syntax.Tactic := do
  `(tactic| guard_expr $(← trExpr (← expr!)) =~ $(← trExpr (← parse (tk ":=" *> pExpr))))

@[tr_tactic guard_target'] def trGuardTarget' : TacM Syntax.Tactic := do
  `(tactic| guard_target =~ $(← trExpr (← parse pExpr)))

@[tr_tactic triv] def trTriv : TacM Syntax.Tactic := `(tactic| triv)

@[tr_tactic use] def trUse : TacM Syntax.Tactic := do
  `(tactic| use $(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*)

@[tr_tactic clear_aux_decl] def trClearAuxDecl : TacM Syntax.Tactic := `(tactic| clear_aux_decl)

attribute [tr_tactic change'] trChange

open Mathlib.Tactic in
@[tr_tactic set] def trSet : TacM Syntax.Tactic := do
  let hSimp := (← parse (tk "!")?).isSome
  let a ← parse ident
  let ty ← parse (tk ":" *> pExpr)?
  let val ← parse (tk ":=") *> parse pExpr
  let revName ← parse (tk "with" *> return (← (tk "<-")?, ← ident))?
  let (rev, name) := match revName with
    | none => (none, none)
    | some (rev, name) => (some (optTk rev.isSome), some (mkIdent name))
  let ty ← ty.mapM (trExpr ·)
  let val ← trExpr val
  let args ← `(setArgsRest| $(mkIdent a):ident $[: $ty]? := $val $[with $[←%$rev]? $name]?)
  if hSimp then
    `(tactic| set! $args:setArgsRest)
  else
    `(tactic| set $args:setArgsRest)

@[tr_tactic clear_except] def trClearExcept : TacM Syntax.Tactic := do
  `(tactic| clear* - $((← parse ident*).map mkIdent)*)

@[tr_tactic extract_goal] def trExtractGoal : TacM Syntax.Tactic := do
  let hSimp ← parse (tk "!")?
  let n := (← parse (ident)?).map mkIdent
  let vs := (← parse (tk "with" *> ident*)?).map (·.map mkIdent)
  match hSimp with
  | none => `(tactic| extract_goal $[$n:ident]? $[with $[$vs]*]?)
  | some _ => `(tactic| extract_goal! $[$n:ident]? $[with $[$vs]*]?)

@[tr_tactic inhabit] def trInhabit : TacM Syntax.Tactic := do
  let t ← trExpr (← parse pExpr)
  `(tactic| inhabit $[$((← parse (ident)?).map mkIdent) :]? $t)

@[tr_tactic revert_deps] def trRevertDeps : TacM Syntax.Tactic := do
  `(tactic| revert_deps $[$((← parse ident*).map mkIdent)]*)

@[tr_tactic revert_after] def trRevertAfter : TacM Syntax.Tactic := do
  `(tactic| revert_after $(mkIdent (← parse ident)))

@[tr_tactic revert_target_deps] def trRevertTargetDeps : TacM Syntax.Tactic :=
  `(tactic| revert_target_deps)

@[tr_tactic clear_value] def trClearValue : TacM Syntax.Tactic := do
  `(tactic| clear_value $[$((← parse ident*).map mkIdent)]*)

attribute [tr_tactic generalize'] trGeneralize

attribute [tr_tactic subst'] trSubst

