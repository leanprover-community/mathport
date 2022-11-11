/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser
open Std.Tactic.RCases

-- # tactic.rcases

mutual

partial def trRCasesPat : RCasesPat → M (TSyntax `rcasesPat)
  | .one BinderName._ => `(rcasesPat| _)
  | .one (BinderName.ident x) => `(rcasesPat| $(mkIdent x):ident)
  | .clear => do `(rcasesPat| -)
  | .explicit pat => do `(rcasesPat| @$(← trRCasesPat pat))
  | .tuple pats => do `(rcasesPat| ⟨$(← pats.mapM trRCasesPatLo),*⟩)
  | .alts #[pat] => trRCasesPat pat
  | pat => do `(rcasesPat| ($(← trRCasesPatLo pat)))

partial def trRCasesPatMed (pat : RCasesPat) : M (TSyntax ``rcasesPatMed) := do
  let pats := match pat with | RCasesPat.alts pats => pats | pat => #[pat]
  `(rcasesPatMed| $[$(← pats.mapM trRCasesPat)]|*)

partial def trRCasesPatLo (pat : RCasesPat) : M (TSyntax ``rcasesPatLo) := do
  let (pat, ty) ← match pat with
    | RCasesPat.typed pat ty => pure (pat, some (← trExpr ty))
    | _ => pure (pat, none)
  `(rcasesPatLo| $(← trRCasesPatMed pat):rcasesPatMed $[: $ty:term]?)

end

@[tr_tactic rcases] def trRCases : TacM Syntax.Tactic := do
  match ← parse rcasesArgs with
  | .hint es depth => do
    let es := match es with | Sum.inl e => #[e] | Sum.inr es => es
    `(tactic| rcases? $[$(← liftM $ es.mapM trExpr):term],*
      $[: $(depth.map Quote.quote)]?)
  | .rcases n e pat => do
    `(tactic| rcases $[$(n.map mkIdent):ident :]? $(← trExpr e):term
              with $(← trRCasesPat pat):rcasesPat)
  | .rcasesMany es pat => liftM $ show M _ from do
    `(tactic| rcases $[$(← es.mapM trExpr):term],* with $(← trRCasesPat pat):rcasesPat)

@[tr_tactic obtain] def trObtain : TacM Syntax.Tactic := do
  let ((pat, ty), vals) ← parse obtainArg
  let vals ← liftM <| vals.mapM (·.mapM trExpr)
  liftM do `(tactic|
    obtain $[$(← pat.mapM trRCasesPatMed):rcasesPatMed]?
      $[: $(← ty.mapM trExpr)]? $[:= $[$vals],*]?)

partial def trRIntroPat : RIntroPat → M (TSyntax `rintroPat)
  | .one pat => do `(rintroPat| $(← trRCasesPat pat):rcasesPat)
  | .binder pats ty => do
    `(rintroPat| ($[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?))

@[tr_tactic rintro rintros] def trRIntro : TacM Syntax.Tactic := do
  match ← parse rintroArg with
  | .inr depth => `(tactic| rintro? $[: $(depth.map Quote.quote)]?)
  | .inl (pats, ty) => show M _ from do
    `(tactic| rintro $[$(← pats.mapM trRIntroPat):rintroPat]* $[: $(← ty.mapM trExpr)]?)

@[tr_tactic rsuffices rsufficesI] def trRSuffices : TacM Syntax.Tactic := do
  let ((pat, ty), vals) ← parse obtainArg
  let vals ← liftM <| vals.mapM (·.mapM trExpr)
  liftM do `(tactic|
    rsuffices $[$(← pat.mapM trRCasesPatMed):rcasesPatMed]?
      $[: $(← ty.mapM trExpr)]? $[:= $[$vals],*]?)
