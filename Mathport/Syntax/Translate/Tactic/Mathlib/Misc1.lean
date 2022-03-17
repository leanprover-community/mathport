/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3
import Mathport.Syntax.Translate.Tactic.Mathlib.Cache

-- Misc. general-purpose tactics

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.by_contra
@[trTactic by_contra'] def trByContra' : TacM Syntax := do
  `(tactic| by_contra' $((← parse (ident)?).map mkIdent)?
    $[: $(← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr)]?)

-- # tactic.dec_trivial
@[trTactic dec_trivial] def trDecTrivial : TacM Syntax := do
  match ← parse (tk "!")? with
  | none => `(tactic| decide)
  | some _ => `(tactic| decide!)

-- # tactic.delta_instance
@[trTactic delta_instance] def trDeltaInstance : TacM Syntax := do
  `(tactic| delta_instance $((← parse ident*).map mkIdent)*)

-- # tactic.elide
@[trTactic elide] def trElide : TacM Syntax := do
  `(tactic| elide $(Quote.quote (← parse smallNat)) $(← trLoc (← parse location))?)

@[trTactic unelide] def trUnelide : TacM Syntax := do
  `(tactic| unelide $(← trLoc (← parse location))?)

-- # tactic.explode
@[trUserCmd «#explode»] def trExplode : TacM Syntax := do
  `(command| #explode $(← mkIdentI (← parse ident)))

-- # tactic.find
@[trUserCmd «#find»] def trFindCmd : TacM Syntax := do
  `(command| #find $(← trExpr (← parse pExpr)))

-- # tactic.find_unused

@[trUserAttr main_declaration] def trMainDeclaration := tagAttr `main_declaration

@[trUserCmd «#list_unused_decls»] def trListUnusedDecls : TacM Syntax :=
  parse_0 `(command| #list_unused_decls)

-- # tactic.generalizes

@[trTactic generalizes] def trGeneralizes : TacM Syntax := do
  let args ← (← parse (listOf generalizesArg)).mapM fun (h, t, x) =>
    return mkNode ``Parser.Tactic.generalizesArg #[
      mkOptionalNode' h fun h => #[mkIdent h, mkAtom ":"],
      ← trExpr t, mkAtom "=", mkIdent x]
  `(tactic| generalizes [$args,*])

-- # tactic.generalize_proofs
@[trTactic generalize_proofs] def trGeneralizeProofs : TacM Syntax := do
  `(tactic| generalize_proofs
    $((← parse (ident_)*).map trBinderIdent)*
    $[$(← trLoc (← parse location))]?)

-- # tactic.induction

@[trUserCmd cases'] def trCases' : TacM Syntax := do
  warn! "unsupported: cases'" -- unattested

@[trUserCmd induction'] def trInduction' : TacM Syntax := do
  warn! "unsupported: induction'" -- unattested

-- # tactic.itauto
@[trTactic itauto] def trITauto : TacM Syntax := do
  match ← parse (tk "!")?, ← parse ((return some (← pExprList)) <|> (tk "*" *> pure none))? with
  | none,   none           => `(tactic| itauto)
  | some _, none           => `(tactic| itauto!)
  | none,   some none      => `(tactic| itauto *)
  | some _, some none      => `(tactic| itauto! *)
  | none,   some (some ls) => `(tactic| itauto [$(← ls.mapM trExpr),*])
  | some _, some (some ls) => `(tactic| itauto! [$(← ls.mapM trExpr),*])

-- # tactic.lift
@[trTactic lift] def trLift : TacM Syntax := do
  `(tactic| lift $(← trExpr (← parse pExpr))
    to $(← trExpr (← parse (tk "to" *> pExpr)))
    $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?
    $[with $(trWithIdentList (← parse withIdentList))*]?)

-- # tactic.lift

-- # tactic.localized

@[trUserCmd «open_locale»] def trOpenLocale : TacM Syntax := do
  `(command| open_locale $(← liftM $ (← parse (ident* <* skipAll)).mapM mkIdentN)*)

@[trUserCmd «localized»] def trLocalized : TacM Unit := do
  let (#[cmd], loc) ← parse $ return (← pExpr *> emittedCodeHere, ← tk "in" *> ident)
    | warn! "unsupported: multiple localized"
  let loc ← renameNamespace loc
  let cmd ← match cmd with
  | Command.attribute true mods attrs ns =>
    let loc ← mkIdentR loc
    trAttributeCmd false attrs ns fun stx => Id.run `(command| localized [$loc] $stx)
  | Command.notation (true, res) attrs n => trNotationCmd (false, res) attrs n loc
  | _ => warn! "unsupported: unusual localized"

-- # tactic.mk_iff_of_inductive_prop
@[trUserCmd «mk_iff_of_inductive_prop»] def trMkIffOfInductiveProp : TacM Syntax := do
  let (i, r) ← parse $ return (← ident, ← ident)
  `(command| mk_iff_of_inductive_prop $(← mkIdentI i) $(← mkIdentI r))

@[trUserAttr mk_iff] def trMkIffAttr : TacM Syntax := do
  `(attr| mk_iff $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

-- # tactic.replacer

@[trUserCmd «def_replacer»] def trDefReplacer : TacM Syntax := do
  let (n, ty) ← parse $ return (← ident, ← (tk ":" *> pExpr)?)
  `(command| def_replacer $(← mkIdentI n) $[$(← trOptType ty):typeSpec]?)

@[trUserAttr replaceable] def trReplaceableAttr := tagAttr `replaceable

-- # tactic.obviously

@[trUserAttr obviously] def trObviouslyAttr := tagAttr `obviously

@[trNITactic obviously] def trObviously (_ : AST3.Expr) : M Syntax := `(tactic| obviously)

-- # tactic.pretty_cases
@[trTactic pretty_cases] def trPrettyCases : TacM Syntax := do
  `(tactic| pretty_cases)

-- # tactic.protected

@[trUserAttr «protected»] def trProtectedAttr := tagAttr `protected

@[trUserAttr protect_proj] def trProtectProjAttr : TacM Syntax := do
  let ids ← match ← parse withoutIdentList with
  | #[] => pure none
  | ids => some <$> liftM (ids.mapM mkIdentF)
  `(attr| protect_proj $[without $ids*]?)

-- # tactic.push_neg

@[trTactic push_neg] def trPushNeg : TacM Syntax := do
  `(tactic| push_neg $(← trLoc (← parse location))?)

@[trTactic contrapose] def trContrapose : TacM Syntax := do
  let (tac, s) := match ← parse (tk "!")? with
  | none => (``Parser.Tactic.contrapose, "contrapose")
  | some _ => (``Parser.Tactic.contrapose!, "contrapose!")
  let n ← parse (return (← ident, ← (tk "with" *> ident)?))?
  pure $ mkNode tac #[mkAtom s, mkOptionalNode' n fun (a, b) =>
    #[mkIdent a, mkOptionalNode' b fun b => #[mkAtom "with", mkIdent b]]]

-- # tactic.rename_var
@[trTactic rename_var] def trRenameVar : TacM Syntax := do
  `(tactic| rename_var $(mkIdent (← parse ident)) → $(mkIdent (← parse ident))
    $(← trLoc (← parse location))?)

-- # tactic.restate_axiom
@[trUserCmd «restate_axiom»] def trRestateAxiom : TacM Syntax := do
  let (a, b) ← parse $ return (← ident, ← (ident)?)
  `(command| restate_axiom $(← mkIdentI a) $(← liftM $ b.mapM mkIdentI)?)

-- # tactic.rewrite
@[trTactic assoc_rewrite assoc_rw] def trAssocRw : TacM Syntax := do
  `(tactic| assoc_rw
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.show_term
@[trTactic show_term] def trShowTerm : TacM Syntax := do
  `(tactic| show_term $(← trBlock (← itactic)):tacticSeq)

-- # tactic.simp_rw
@[trTactic simp_rw] def trSimpRw : TacM Syntax := do
  `(tactic| simp_rw
    [$(← liftM $ (← parse rwRules).mapM trRwRule),*]
    $(← trLoc (← parse location))?)

-- # tactic.simp_command
@[trUserCmd «#simp»] def trSimpCmd : TacM Syntax := do
  let (o, args, attrs, e) ← parse $
    return (← onlyFlag, ← simpArgList, (← (tk "with" *> ident*)?).getD #[], ← (tk ":")? *> pExpr)
  let hs := trSimpList (← trSimpArgs args)
  let o := if o then mkNullNode #[mkAtom "only"] else mkNullNode
  let colon := if attrs.isEmpty then mkNullNode else mkNullNode #[mkAtom ":"]
  pure $ mkNode ``Parser.Command.simp #[mkAtom "#simp",
    o, hs, trSimpAttrs attrs, colon, ← trExpr e]

-- # tactic.simp_result
@[trTactic dsimp_result] def trDSimpResult : TacM Syntax := do
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  pure $ mkNode ``Parser.Tactic.dsimpResult #[mkAtom "dsimp_result", o, hs,
    trSimpAttrs $ (← parse (tk "with" *> ident*)?).getD #[],
    mkAtom "=>", ← trBlock (← itactic)]

@[trTactic simp_result] def trSimpResult : TacM Syntax := do
  let o := if ← parse onlyFlag then mkNullNode #[mkAtom "only"] else mkNullNode
  let hs := trSimpList (← trSimpArgs (← parse simpArgList))
  pure $ mkNode ``Parser.Tactic.simpResult #[mkAtom "simp_result", o, hs,
    trSimpAttrs $ (← parse (tk "with" *> ident*)?).getD #[],
    mkAtom "=>", ← trBlock (← itactic)]

-- # tactic.simpa
@[trTactic simpa] def trSimpa : TacM Syntax := do
  let unfold := (← parse (tk "!")?).map fun _ => default
  let squeeze := (← parse (tk "?")?).map fun _ => default
  let o := if ← parse onlyFlag then some default else none
  let hs := some (← trSimpArgs (← parse simpArgList)) |>.filter (!·.isEmpty)
  let attrs := (← parse (tk "with" *> ident*)?).map (·.map mkIdent)
  let e ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  let (cfg, disch) ← parseSimpConfigCore (← expr?)
  let cfg := cfg.bind quoteSimpConfig
  `(tactic| simpa $[!%$unfold]? $[?%$squeeze]? $[(config := $cfg)]? $[(disch := $disch:tactic)]?
      $[only%$o]? $[[$hs,*]]? $[with $attrs*]? $[using $e]?)

-- # tactic.split_ifs
@[trTactic split_ifs] def trSplitIfs : TacM Syntax := do
  `(tactic| split_ifs $(← trLoc (← parse location))?
    $[with $(trWithIdentList (← parse withIdentList))*]?)

-- # tactic.swap_var
@[trTactic swap_var] def trSwapVar : TacM Syntax := do
  let args ← parse $ maybeListOf $ return (← ident, ← (tk "↔" <|> tk "<->")? *> ident)
  if args.isEmpty then `(tactic| skip) else
  let args ← args.mapM fun (x, y) =>
    `(Parser.Tactic.swapVarArg| $(mkIdent x):ident ↔ $(mkIdent y):ident)
  `(tactic| swap_var $args,*)

-- # tactic.tauto
@[trTactic tauto tautology] def trTauto : TacM Syntax := do
  let c ← parse (tk "!")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match c with
  | none => `(tactic| tauto $[(config := $cfg)]?)
  | some _ => `(tactic| tauto! $[(config := $cfg)]?)

-- # tactic.unify_equations
@[trTactic unify_equations] def trUnifyEquations : TacM Syntax := do
  warn! "unsupported tactic unify_equations" -- unattested

-- # tactic.where
@[trUserCmd «#where»] def trWhereCmd : TacM Syntax := parse skipAll *> `(command| #where)

-- # tactic.tfae
@[trTactic tfae_have] def trTfaeHave : TacM Syntax :=
  return mkNode ``Parser.Tactic.tfaeHave #[mkAtom "tfae_have",
    mkOptionalNode' (← parse ((ident)? <* tk ":")) fun h => #[mkIdent h, mkAtom ":"],
    Quote.quote (← parse smallNat),
    mkAtom (← parse ((tk "->" *> pure "→") <|> (tk "↔" *> pure "↔") <|> (tk "<-" *> pure "←"))),
    Quote.quote (← parse smallNat)]

@[trTactic tfae_finish] def trTfaeFinish : TacM Syntax := `(tactic| tfae_finish)

-- # tactic.apply_fun
@[trTactic apply_fun] def trApplyFun : TacM Syntax := do
  `(tactic| apply_fun
    $(← trExpr (← parse pExpr))
    $[$(← trLoc (← parse location))]?
    $[using $(← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr)]?)

-- # tactic.reassoc_axiom

@[trUserAttr reassoc] def trReassocAttr : TacM Syntax := do
  `(attr| reassoc $(← liftM $ (← parse (ident)?).mapM mkIdentI)?)

@[trUserCmd «reassoc_axiom»] def trReassocAxiom : TacM Syntax := do
  `(command| reassoc_axiom $(← mkIdentI (← parse ident)))

@[trTactic reassoc] def trReassoc : TacM Syntax := do
  match ← parse (tk "!")?, (← parse ident*).map mkIdent with
  | none, ns => `(tactic| reassoc $ns*)
  | some _, ns => `(tactic| reassoc! $ns*)

@[trNITactic tactic.derive_reassoc_proof] def trDeriveReassocProof
  (_ : AST3.Expr) : M Syntax := `(tactic| derive_reassoc_proof)

-- # tactic.slice

@[trConv slice] def trSliceConv : TacM Syntax := do
  let ⟨_, AST3.Expr.nat a⟩ ← expr! | warn! "slice: weird nat"
  let ⟨_, AST3.Expr.nat b⟩ ← expr! | warn! "slice: weird nat"
  `(conv| slice $(Quote.quote a) $(Quote.quote b))

@[trTactic slice_lhs] def trSliceLHS : TacM Syntax := do
  `(tactic| slice_lhs $(Quote.quote (← parse smallNat)) $(Quote.quote (← parse smallNat))
    => $(← trConvBlock (← itactic)):convSeq)

@[trTactic slice_rhs] def trSliceRHS : TacM Syntax := do
  `(tactic| slice_rhs $(Quote.quote (← parse smallNat)) $(Quote.quote (← parse smallNat))
    => $(← trConvBlock (← itactic)):convSeq)

-- # tactic.rewrite_search

@[trUserAttr rewrite] def trRewriteAttr := tagAttr `rewrite

@[trTactic rewrite_search] def trRewriteSearch : TacM Syntax := do
  let explain ← parse (tk "?")?
  let rw ← liftM $ (← parse rwRules).mapM trRwRule
  let cfg ← liftM $ (← expr?).mapM trExpr
  match explain with
  | none => `(tactic| rw_search $[(config := $cfg)]? [$rw,*])
  | some _ => `(tactic| rw_search? $[(config := $cfg)]? [$rw,*])

-- # tactic.tidy

@[trUserAttr tidy] def trTidyAttr := tagAttr `tidy

@[trTactic tidy] def trTidy : TacM Syntax := do
  let explain ← parse (tk "?")?
  let cfg ← liftM $ (← expr?).mapM trExpr
  match explain with
  | none => `(tactic| tidy $[(config := $cfg)]?)
  | some _ => `(tactic| tidy? $[(config := $cfg)]?)

-- # tactic.wlog
@[trTactic wlog] def trWlog : TacM Syntax := do
  let h := (← parse (ident)?).map mkIdent
  let pat ← liftM $ (← parse (tk ":" *> pExpr)?).mapM trExpr
  let cases ← liftM $ (← parse (tk ":=" *> pExpr)?).mapM trExpr
  let perms ← parse (tk "using" *> (listOf ident* <|> return #[← ident*]))?
  let perms := match perms.getD #[] with
  | #[] => none
  | perms => some (perms.map (·.map mkIdent))
  let disch ← liftM $ (← expr?).mapM trExpr
  `(tactic| wlog $[(discharger := $disch)]? $(h)? $[: $pat]? $[:= $cases]? $[using $[$perms*],*]?)

-- # tactic.algebra
@[trUserAttr ancestor] def trAncestorAttr : TacM Syntax := do
  `(attr| ancestor $(← liftM $ (← parse ident*).mapM mkIdentI)*)
