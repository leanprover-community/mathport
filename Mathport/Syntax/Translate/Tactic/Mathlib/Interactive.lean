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

@[trTactic fconstructor] def trFConstructor : TacM Syntax := `(tactic| fconstructor)

@[trTactic try_for] def trTryFor : TacM Syntax := do
  `(tactic| try_for $(← trExpr (← parse pExpr)) $(← trBlock (← itactic)):tacticSeq)

@[trTactic substs] def trSubsts : TacM Syntax := do
  `(tactic| substs $[$((← parse ident*).map mkIdent)]*)

@[trTactic unfold_coes] def trUnfoldCoes : TacM Syntax := do
  `(tactic| unfold_coes $(← trLoc (← parse location))?)

@[trTactic unfold_wf] def trUnfoldWf : TacM Syntax := `(tactic| unfold_wf)

@[trTactic unfold_aux] def trUnfoldAux : TacM Syntax := `(tactic| unfold_aux)

@[trTactic recover] def trRecover : TacM Syntax := `(tactic| recover)

@[trTactic «continue»] def trContinue : TacM Syntax := do
  `(tactic| continue $(← trBlock (← itactic)):tacticSeq)

@[trTactic id] def trId : TacM Syntax := do trIdTactic (← itactic)

@[trTactic work_on_goal] def trWorkOnGoal : TacM Syntax := do
  `(tactic| on_goal $(Quote.quote (← parse smallNat)) =>
    $(← trBlock (← itactic)):tacticSeq)

@[trTactic swap] def trSwap : TacM Syntax := do
  let n ← (← expr?).mapM fun
  | ⟨_, AST3.Expr.nat n⟩ => pure n
  | _ => warn! "unsupported: weird nat"
  match n.getD 2 with
  | 1 => `(tactic| skip)
  | 2 => `(tactic| swap)
  | n => `(tactic| pick_goal $(Quote.quote n))

@[trTactic rotate] def trRotate : TacM Syntax := do
  let n ← (← expr?).mapM fun
  | ⟨_, AST3.Expr.nat n⟩ => pure n
  | _ => warn! "unsupported: weird nat"
  match n.getD 1 with
  | 0 => `(tactic| skip)
  | 1 => `(tactic| rotate_left)
  | n => `(tactic| rotate_left $(Quote.quote n))

@[trTactic clear_] def trClear_ : TacM Syntax := `(tactic| clear_)

@[trTactic replace] def trReplace : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  let ty ← (← parse (tk ":" *> pExpr)?).mapM (trExpr ·)
  match ← parse (tk ":=" *> pExpr)? with
  | some pr => `(tactic| replace $[$h]? $[: $ty]? := $(← trExpr pr))
  | none =>  `(tactic| replace $[$h]? $[: $ty]?)

@[trTactic classical] def trClassical : TacM Syntax := `(tactic| classical)

@[trTactic generalize_hyp] def trGeneralizeHyp : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  parse (tk ":")
  let (e, x) ← parse generalizeArg
  let e ← trExpr e; let x := mkIdent x
  match ← trLoc (← parse location) with
  | none => `(tactic| generalize $[$h :]? $e = $x)
  | some loc => `(tactic| generalize $[$h :]? $e = $x $loc)

@[trTactic clean] def trClean : TacM Syntax := do
  `(tactic| clean $(← trExpr (← parse pExpr)))

@[trTactic refine_struct] def trRefineStruct : TacM Syntax := do
  `(tactic| refine_struct $(← trExpr (← parse pExpr)))

@[trTactic guard_hyp'] def trGuardHyp' : TacM Syntax := do
  `(tactic| guard_hyp $(mkIdent (← parse ident)) : $(← trExpr (← parse (tk ":" *> pExpr))))

@[trTactic match_hyp] def trMatchHyp : TacM Syntax := do
  let h := mkIdent (← parse ident)
  let ty ← trExpr (← parse (tk ":" *> pExpr))
  let m ← liftM $ (← expr?).mapM trExpr
  `(tactic| match_hyp $[(m := $m)]? $h : $ty)

@[trTactic guard_expr_strict] def trGuardExprStrict : TacM Syntax := do
  let t ← expr!
  let p ← parse (tk ":=" *> pExpr)
  `(tactic| guard_expr $(← trExpr t):term == $(← trExpr p):term)

@[trTactic guard_target_strict] def trGuardTargetStrict : TacM Syntax := do
  `(tactic| guard_target == $(← trExpr (← parse pExpr)))

@[trTactic guard_hyp_strict] def trGuardHypStrict : TacM Syntax := do
  `(tactic| guard_hyp $(mkIdent (← parse ident)) : $(← trExpr (← parse (tk ":" *> pExpr))))

@[trTactic guard_hyp_nums] def trGuardHypNums : TacM Syntax := do
  match (← expr!).kind.unparen with
  | AST3.Expr.nat n => `(tactic| guard_hyp_nums $(Quote.quote n))
  | _ => warn! "unsupported: weird nat"

@[trTactic guard_tags] def trGuardTags : TacM Syntax := do
  `(tactic| guard_tags $[$((← parse ident*).map mkIdent)]*)

@[trTactic guard_proof_term] def trGuardProofTerm : TacM Syntax := do
  `(tactic| guard_proof_term $(← trIdTactic (← itactic)) => $(← trExpr (← parse pExpr)))

@[trTactic success_if_fail_with_msg] def trSuccessIfFailWithMsg : TacM Syntax := do
  let t ← trBlock (← itactic)
  match (← expr!).kind.unparen with
  | AST3.Expr.string s => `(tactic| fail_if_success? $(Syntax.mkStrLit s) $t:tacticSeq)
  | _ => warn! "unsupported: weird string"

@[trTactic field] def trField : TacM Syntax := do
  `(tactic| field $(mkIdent (← parse ident)) => $(← trBlock (← itactic)):tacticSeq)

@[trTactic have_field] def trHaveField : TacM Syntax := `(tactic| have_field)

@[trTactic apply_field] def trApplyField : TacM Syntax := `(tactic| apply_field)

@[trTactic apply_rules] def trApplyRules : TacM Syntax := do
  let hs ← liftM $ (← parse pExprListOrTExpr).mapM trExpr
  let n ← (← expr?).mapM fun
  | ⟨_, AST3.Expr.nat n⟩ => pure $ Quote.quote n
  | _ => warn! "unsupported: weird nat"
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| apply_rules $[(config := $cfg)]? [$hs,*] $(n)?)

@[trTactic h_generalize] def trHGeneralize : TacM Syntax := do
  let rev ← parse (tk "!")?
  let h := (← parse (ident_)?).map trBinderIdent
  let (e, x) ← parse (tk ":") *> parse hGeneralizeArg
  let e ← trExpr e; let x := mkIdent x
  let eqsH := (← parse (tk "with" *> ident_)?).map trBinderIdent
  match rev with
  | none => `(tactic| h_generalize $[$h :]? $e = $x $[with $eqsH]?)
  | some _ => `(tactic| h_generalize! $[$h :]? $e = $x $[with $eqsH]?)

@[trTactic guard_expr_eq'] def trGuardExprEq' : TacM Syntax := do
  `(tactic| guard_expr $(← trExpr (← expr!)) = $(← trExpr (← parse (tk ":=" *> pExpr))))

@[trTactic guard_target'] def trGuardTarget' : TacM Syntax := do
  `(tactic| guard_target = $(← trExpr (← parse pExpr)))

@[trTactic triv] def trTriv : TacM Syntax := `(tactic| triv)

@[trTactic use] def trUse : TacM Syntax := do
  `(tactic| use $(← liftM $ (← parse pExprListOrTExpr).mapM trExpr),*)

@[trTactic clear_aux_decl] def trClearAuxDecl : TacM Syntax := `(tactic| clear_aux_decl)

attribute [trTactic change'] trChange

open Mathlib.Tactic in
@[trTactic set] def trSet : TacM Syntax := do
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

@[trTactic clear_except] def trClearExcept : TacM Syntax := do
  `(tactic| clear* - $((← parse ident*).map mkIdent)*)

@[trTactic extract_goal] def trExtractGoal : TacM Syntax := do
  let hSimp ← parse (tk "!")?
  let n := (← parse (ident)?).map mkIdent
  let vs := (← parse (tk "with" *> ident*)?).map (·.map mkIdent)
  match hSimp with
  | none => `(tactic| extract_goal $[$n:ident]? $[with $[$vs]*]?)
  | some _ => `(tactic| extract_goal! $[$n:ident]? $[with $[$vs]*]?)

@[trTactic inhabit] def trInhabit : TacM Syntax := do
  let t ← trExpr (← parse pExpr)
  `(tactic| inhabit $[$((← parse (ident)?).map mkIdent) :]? $t)

@[trTactic revert_deps] def trRevertDeps : TacM Syntax := do
  `(tactic| revert_deps $[$((← parse ident*).map mkIdent)]*)

@[trTactic revert_after] def trRevertAfter : TacM Syntax := do
  `(tactic| revert_after $(mkIdent (← parse ident)))

@[trTactic revert_target_deps] def trRevertTargetDeps : TacM Syntax :=
  `(tactic| revert_target_deps)

@[trTactic clear_value] def trClearValue : TacM Syntax := do
  `(tactic| clear_value $[$((← parse ident*).map mkIdent)]*)

attribute [trTactic generalize'] trGeneralize

attribute [trTactic subst'] trSubst

