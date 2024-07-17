/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3
import Mathport.Syntax.Translate.Tactic.Mathlib.Cache
import Mathport.Syntax.Translate.Command
import Mathlib.Tactic.Explode
import Mathlib.Tactic.RewriteSearch

-- Misc. general-purpose tactics

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.by_contra
@[tr_tactic by_contra'] def trByContra' : TacM Syntax.Tactic := do
  `(tactic| by_contra! $[$((← parse (ident)?).map mkIdent):ident]?
    $[: $(← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr)]?)

-- # tactic.dec_trivial
@[tr_tactic dec_trivial] def trDecTrivial : TacM Syntax.Tactic := do
  match ← parse (tk "!")? with
  | none => `(tactic| decide)
  | some _ => `(tactic| decide!)

-- # tactic.delta_instance
@[tr_tactic delta_instance] def trDeltaInstance : TacM Syntax.Tactic := do
  `(tactic| delta_instance $[$((← parse ident*).map mkIdent)]*)

-- # tactic.elide
@[tr_tactic elide] def trElide : TacM Syntax.Tactic := do
  `(tactic| elide $(Quote.quote (← parse smallNat)) $(← trLoc (← parse location))?)

@[tr_tactic unelide] def trUnelide : TacM Syntax.Tactic := do
  `(tactic| unelide $(← trLoc (← parse location))?)

-- # tactic.explode
@[tr_user_cmd «#explode»] def trExplode : Parse1 Syntax.Command :=
  parse1 ident fun n => do `(command| #explode $(← mkIdentI n))

-- # tactic.find
@[tr_user_cmd «#find»] def trFindCmd : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do `(command| #find $(← trExpr e))

-- # tactic.find_unused

@[tr_user_attr main_declaration] def trMainDeclaration := tagAttr `main_declaration

@[tr_user_cmd «#list_unused_decls»] def trListUnusedDecls : Parse1 Syntax.Command :=
  parse0 `(command| #list_unused_decls)

-- # tactic.generalizes

@[tr_tactic generalizes] def trGeneralizes : TacM Syntax.Tactic := do
  let args ← (← parse (listOf generalizesArg)).mapM fun (h, t, x) => do
    `(Parser.Tactic.generalizeArg| $[$(h.map mkIdent) :]? $(← trExpr t) = $(mkIdent x))
  `(tactic| generalize $args,*)

-- # tactic.generalize_proofs
@[tr_tactic generalize_proofs] def trGeneralizeProofs : TacM Syntax.Tactic := do
  `(tactic| generalize_proofs
    $[$((← parse (ident_)*).map trBinderIdent)]*
    $[$(← trLoc (← parse location))]?)

-- # tactic.induction

@[tr_user_cmd cases'] def trCases' : Parse1 Syntax.Command := parse0 do
  warn! "unsupported: cases'" -- unattested

@[tr_user_cmd induction'] def trInduction' : Parse1 Syntax.Command := parse0 do
  warn! "unsupported: induction'" -- unattested

-- # tactic.itauto
@[tr_tactic itauto] def trITauto : TacM Syntax.Tactic := do
  match ← parse (tk "!")?, ← parse ((return some (← pExprList)) <|> (tk "*" *> pure none))? with
  | none,   none           => `(tactic| itauto)
  | some _, none           => `(tactic| itauto!)
  | none,   some none      => `(tactic| itauto *)
  | some _, some none      => `(tactic| itauto! *)
  | none,   some (some ls) => `(tactic| itauto [$(← ls.mapM trExpr),*])
  | some _, some (some ls) => `(tactic| itauto! [$(← ls.mapM trExpr),*])

-- # tactic.lift
@[tr_tactic lift] def trLift : TacM Syntax.Tactic := do
  let what ← trExpr (← parse pExpr)
  let to_ ← trExpr (← parse (tk "to" *> pExpr))
  let using_ ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let with_ ← (← parse withIdentList).toList.mapM fun
    | .ident n => pure <| mkIdent n
    | _ => warn! "unsupported: lift with _" | pure <| mkIdent `_
  match with_ with
  | [] => `(tactic| lift $what to $to_ $[using $using_]?)
  | [w1] => `(tactic| lift $what to $to_ $[using $using_]? with $w1)
  | [w1, w2] => `(tactic| lift $what to $to_ $[using $using_]? with $w1 $w2)
  | w1::w2::w3::_ => `(tactic| lift $what to $to_ $[using $using_]? with $w1 $w2 $w3)

-- # tactic.lift

-- # tactic.localized

@[tr_user_cmd «open_locale»] def trOpenLocale : Parse1 Unit :=
  parse1 (ident* <* skipAll) fun ids => do
  unless ids.isEmpty do
    pushM `(command| open scoped $(← liftM $ ids.mapM mkIdentN)*)

@[tr_user_cmd «localized»] def trLocalized : Parse1 Unit :=
  parse1 (return (← pExpr *> emittedCodeHere, ← tk "in" *> ident)) fun (cmd, loc) => do
  let loc ← renameNamespace loc
  match cmd with
  | #[Command.attribute true mods attrs ns] =>
    unless mods.isEmpty do warn! "unsupported: localized modifiers"
    if loc == (← getCurrNamespace) then
      trAttributeCmd .scoped attrs ns id
    else
      let loc ← mkIdentR loc
      trAttributeCmd .global attrs ns fun stx => Id.run `(scoped[$loc] $stx)
  | #[Command.notation (true, res) attrs n] =>
    if loc == (← getCurrNamespace) then
      trNotationCmd .scoped res attrs n
    else
      trNotationCmd .global res attrs n (some loc)
  | #[_] => warn! "unsupported: unusual localized"
  | _ => warn! "unsupported: multiple localized"

-- # tactic.mk_iff_of_inductive_prop
@[tr_user_cmd «mk_iff_of_inductive_prop»] def trMkIffOfInductiveProp : Parse1 Syntax.Command :=
  parse1 (return (← ident, ← ident)) fun (i, r) => do
  `(command| mk_iff_of_inductive_prop $(← mkIdentI i) $(← mkIdentI r))

@[tr_user_attr mk_iff] def trMkIffAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun n => do `(attr| mk_iff $(← liftM $ n.mapM mkIdentI)?)

-- # tactic.replacer

@[tr_user_cmd «def_replacer»] def trDefReplacer : Parse1 Syntax.Command :=
  parse1 (return (← ident, ← (tk ":" *> pExpr)?)) fun (n, ty) => do
  `(command| def_replacer $(← mkIdentI n) $[$(← trOptType ty):typeSpec]?)

@[tr_user_attr replaceable] def trReplaceableAttr := tagAttr `replaceable

-- # tactic.obviously

@[tr_user_attr obviously] def trObviouslyAttr := tagAttr `obviously

@[tr_ni_tactic obviously] def trObviously (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| obviously)

-- # tactic.pretty_cases
@[tr_tactic pretty_cases] def trPrettyCases : TacM Syntax.Tactic := do
  `(tactic| pretty_cases)

-- # tactic.protected

@[tr_user_attr «protected»] def trProtectedAttr := tagAttr `protected

@[tr_user_attr protect_proj] def trProtectProjAttr : Parse1 Syntax.Attr :=
  parse1 withoutIdentList fun ids => do
  let ids ← match ids with
  | #[] => pure none
  | ids => some <$> liftM (ids.mapM mkIdentF)
  `(attr| protect_proj $[without $[$ids]*]?)

-- # tactic.push_neg

@[tr_tactic push_neg] def trPushNeg : TacM Syntax.Tactic := do
  `(tactic| push_neg $(← trLoc (← parse location))?)

@[tr_user_cmd «#push_neg»] def trPushNegCmd : Parse1 Syntax.Command :=
  parse1 pExpr fun e => do `(command| #push_neg $(← trExpr e))

@[tr_tactic contrapose] def trContrapose : TacM Syntax.Tactic := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Mathlib.Tactic.Contrapose.contrapose, "contrapose")
  | some _ => (``Mathlib.Tactic.Contrapose.contrapose!, "contrapose!")
  let n ← parse (return (← ident, ← (tk "with" *> ident)?))?
  pure ⟨mkNode tac #[mkAtom s, mkOptionalNode' n fun (a, b) =>
    #[mkIdent a, mkOptionalNode' b fun b => #[mkAtom "with", mkIdent b]]]⟩

-- # tactic.rename_var
@[tr_tactic rename_var] def trRenameVar : TacM Syntax.Tactic := do
  `(tactic| rename_bvar $(mkIdent (← parse ident)) → $(mkIdent (← parse ident))
    $(← trLoc (← parse location))?)

-- # tactic.restate_axiom
@[tr_user_cmd «restate_axiom»] def trRestateAxiom : Parse1 Unit :=
  parse1 (return (← ident, ← (ident)?)) fun (_, _) => do
  pure () -- `(command| restate_axiom $(← mkIdentI a) $(← liftM $ b.mapM mkIdentI)?)

-- # tactic.rewrite
@[tr_tactic assoc_rewrite assoc_rw] def trAssocRw : TacM Syntax.Tactic := do
  `(tactic| assoc_rw
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.show_term
@[tr_tactic «show_term»] def trShowTerm : TacM Syntax.Tactic := do
  `(tactic| show_term $(← trBlock (← itactic)):tacticSeq)

-- # tactic.simp_rw
@[tr_tactic simp_rw] def trSimpRw : TacM Syntax.Tactic := do
  `(tactic| simp_rw
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.simp_command
@[tr_user_cmd «#simp»] def trSimpCmd : Parse1 Syntax.Command :=
  parse1 (return (← onlyFlag, ← simpArgList,
    (← (tk "with" *> ident*)?).getD #[], ← (tk ":")? *> pExpr))
  fun (o, args, attrs, e) => do
    let o := optTk o
    let hs ← trSimpArgs args
    let hs := (hs ++ attrs.map trSimpExt).asNonempty
    `(command| #simp $[only%$o]? $[[$hs,*]]? $(← trExpr e))

-- # tactic.simp_result
@[tr_tactic dsimp_result] def trDSimpResult : TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let (hs, _all) := filterSimpStar hs -- dsimp [*] is always pointless
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  `(tactic| dsimp_result $[only%$o]? $[[$hs,*]]? => $(← trBlock (← itactic)))

@[tr_tactic simp_result] def trSimpResult : TacM Syntax.Tactic := do
  let o := optTk (← parse onlyFlag)
  let hs ← trSimpArgs (← parse simpArgList)
  let attrs := (← parse (tk "with" *> ident*)?).getD #[]
  let hs := (hs ++ attrs.map trSimpExt).asNonempty
  `(tactic| simp_result $[only%$o]? $[[$hs,*]]? => $(← trBlock (← itactic)))

-- # tactic.split_ifs
@[tr_tactic split_ifs] def trSplitIfs : TacM Syntax.Tactic := do
  `(tactic| split_ifs $(← trLoc (← parse location))?
    $[with $(((← parse withIdentList).map trBinderIdent).asNonempty)*]?)

-- # tactic.swap_var
@[tr_tactic swap_var] def trSwapVar : TacM Syntax.Tactic := do
  let args ← parse $ maybeListOf $ return (← ident, ← (tk "↔" <|> tk "<->")? *> ident)
  if args.isEmpty then `(tactic| skip) else
  let args ← args.mapM fun (x, y) =>
    `(Mathlib.Tactic.swapRule| $(mkIdent x):ident ↔ $(mkIdent y):ident)
  `(tactic| swap_var $args,*)

-- # tactic.tauto
@[tr_tactic tauto tautology] def trTauto : TacM Syntax.Tactic := do
  let _ ← parse (tk "!")?
  -- Ignore the !.  The new tauto is equivalent to the old tauto!, and the old
  -- tauto is just a half baked weak version of the same thing.
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| tauto $[(config := $cfg)]?)

-- # tactic.unify_equations
@[tr_tactic unify_equations] def trUnifyEquations : TacM Syntax.Tactic := do
  warn! "unsupported tactic unify_equations" -- unattested

-- # tactic.where
@[tr_user_cmd «#where»] def trWhereCmd : Parse1 Syntax.Command :=
  parse1 skipAll fun _ => `(command| #where)

-- # tactic.tfae
open TSyntax.Compat in
@[tr_tactic tfae_have] def trTfaeHave : TacM Syntax.Tactic := do
  let h := (← parse ((ident)? <* tk ":")).map mkIdent
  let n1 := Quote.quote (← parse smallNat)
  let tk ← parse <| (tk "->" *> pure "→") <|> (tk "↔" *> pure "↔") <|> (tk "<-" *> pure "←")
  let n2 := Quote.quote (← parse smallNat)
  match tk with
  | "→" => `(tactic| tfae_have $[$h :]? $n1 → $n2)
  | "↔" => `(tactic| tfae_have $[$h :]? $n1 ↔ $n2)
  | "←" => `(tactic| tfae_have $[$h :]? $n1 ← $n2)
  | _ => unreachable!

@[tr_tactic tfae_finish] def trTfaeFinish : TacM Syntax.Tactic := `(tactic| tfae_finish)

-- # tactic.apply_fun
@[tr_tactic apply_fun] def trApplyFun : TacM Syntax.Tactic := do
  `(tactic| apply_fun
    $(← trExpr (← parse pExpr))
    $[$(← trLoc (← parse location))]?
    $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?)

-- # tactic.reassoc_axiom

@[tr_user_attr reassoc] def trReassocAttr : Parse1 Syntax.Attr :=
  parse1 (ident)? fun n => do
    let ns ← liftM $ n.mapM mkIdentI
    if let some ns := ns then warn! "unsupported lemma name {ns} in reassoc attr"
    `(attr| reassoc)

@[tr_user_cmd «reassoc_axiom»] def trReassocAxiom : Parse1 Syntax.Command :=
  parse1 ident fun n => do `(command| reassoc_axiom $(← mkIdentI n))

@[tr_tactic reassoc] def trReassoc : TacM Syntax.Tactic := do
  match ← parse (tk "!")?, (← parse ident*).map mkIdent with
  | none, ns => `(tactic| reassoc $[$ns]*)
  | some _, ns => `(tactic| reassoc! $[$ns]*)

@[tr_ni_tactic tactic.derive_reassoc_proof] def trDeriveReassocProof
  (_ : AST3.Expr) : M Syntax.Tactic := `(tactic| derive_reassoc_proof)

-- # tactic.slice

@[tr_conv slice] def trSliceConv : TacM Syntax.Conv := do
  let ⟨_, AST3.Expr.nat a⟩ ← expr! | warn! "slice: weird nat"
  let ⟨_, AST3.Expr.nat b⟩ ← expr! | warn! "slice: weird nat"
  `(conv| slice $(Quote.quote a) $(Quote.quote b))

@[tr_tactic slice_lhs] def trSliceLHS : TacM Syntax.Tactic := do
  `(tactic| slice_lhs $(Quote.quote (← parse smallNat)) $(Quote.quote (← parse smallNat))
    => $(← trConvBlock (← itactic)):convSeq)

@[tr_tactic slice_rhs] def trSliceRHS : TacM Syntax.Tactic := do
  `(tactic| slice_rhs $(Quote.quote (← parse smallNat)) $(Quote.quote (← parse smallNat))
    => $(← trConvBlock (← itactic)):convSeq)

-- # tactic.rewrite_search

@[tr_user_attr rewrite] def trRewriteAttr := tagAttr `rewrite

@[tr_tactic rewrite_search] def trRewriteSearch : TacM Syntax.Tactic := do
  let .none ← parse (tk "?")? | warn! "unsupported: rw_search?"
  let #[] ← parse rwRules | warn! "unsupported: rw_search extra args"
  let .none ← expr? | warn! "unsupported: rw_search config"
  `(tactic| rw_search)

-- # tactic.tidy

@[tr_user_attr tidy] def trTidyAttr := tagAttr `tidy

@[tr_tactic tidy] def trTidy : TacM Syntax.Tactic := do
  let explain ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match explain with
  | none => `(tactic| tidy $[(config := $cfg)]?)
  | some _ => `(tactic| tidy? $[(config := $cfg)]?)

-- # tactic.wlog
@[tr_tactic wlog] def trWlog : TacM Syntax.Tactic := do
  let h ← parse (mkIdent <$> ident)
  let pat ← trExpr (← parse (tk ":" *> pExpr))
  let revert ← parse <| tk "generalizing" *>
    ((tk "*" *> pure none) <|> (some <$> (mkIdent <$> ident)*)) <|> pure none
  let H ← parse (tk "with" *> mkIdent <$> ident)?
  `(tactic| wlog $h:ident : $pat:term $[generalizing $[$revert]*]? $[with $H:ident]?)

-- # tactic.algebra
@[tr_user_attr ancestor] def trAncestorAttr : Parse1 Syntax.Attr :=
  parse1 ident* fun _ => pure ⟨.missing⟩ -- ancestor attribute no longer needed
