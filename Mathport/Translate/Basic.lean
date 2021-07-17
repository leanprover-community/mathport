/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.AST3
import Mathport.Data4
import Mathport.Parse
import Mathport.Translate.Notation
import Mathport.Translate.Attributes

namespace Mathport

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open Lean.Elab (Visibility)

namespace Translate

open Std (HashMap)
open AST3

syntax (name := cmdQuot) "`(command|" incQuotDepth(command) ")" : term

local elab:max "throw!" interpStr:interpolatedStr(term) : term <= ty => do
  let pos ← Elab.getRefPosition
  let head := Syntax.mkStrLit $ mkErrorStringWithPos (← read).fileName pos ""
  let str ← Elab.liftMacroM <| interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
  Elab.Term.elabTerm (← `(throw ($head ++ $str))) ty

open Lean Elab Term Quotation in
@[termElab cmdQuot] def elabCmdQuot : TermElab := adaptExpander stxQuot.expand

structure Scope where
  oldStructureCmd : Bool := false
  deriving Inhabited

structure State where
  «prelude» : Bool := false
  imports : Array Name := #[]
  commands : Array Syntax := #[]
  current : Scope := {}
  scopes : Array Scope := #[]
  notations : HashMap String NotationEntry := predefinedNotations
  simpSets : NameSet := predefinedSimpSets
  deriving Inhabited

abbrev M := EStateM String State

local instance : MonadQuotation M where
  getRef              := pure Syntax.missing
  withRef             := fun _ => id
  getCurrMacroScope   := pure 0
  getMainModule       := pure `_fakeMod
  withFreshMacroScope := id

def push (stx : Syntax) : M Unit :=
  modify fun s => { s with commands := s.commands.push stx }

def pushM (stx : M Syntax) : M Unit := stx >>= push

def modifyScope (f : Scope → Scope) : M Unit :=
  modify fun s => { s with current := f s.current }

def pushScope : M Unit :=
  modify fun s => { s with scopes := s.scopes.push s.current }

def popScope : M Unit :=
  modify fun s => match s.scopes.back? with
  | none => s
  | some c => { s with current := c, scopes := s.scopes.pop }

def trDocComment (doc : String) : Syntax :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ "-/")]

partial def scientificLitOfDecimal (num den : Nat) : Option Syntax :=
  findExp num den 0 |>.map fun (m, e) =>
    let str := toString m
    if e == str.length then
      Syntax.mkScientificLit ("0." ++ str)
    else if e < str.length then
      let mStr := str.extract 0 (str.length - e)
      let eStr := str.extract (str.length - e) str.length
      Syntax.mkScientificLit (mStr ++ "." ++ eStr)
    else
      Syntax.mkScientificLit (str ++ "e-" ++ toString e)
where
  findExp n d exp :=
    if d % 10 == 0 then findExp n (d / 10) (exp + 1)
    else if d == 1 then some (n, exp)
    else if d % 2 == 0 then findExp (n * 5) (d / 2) (exp + 1)
    else if d % 5 == 0 then findExp (n * 2) (d / 5) (exp + 1)
    else none

structure BinderContext where
  -- if true, only allow simple for no type
  allowSimple : Option Bool := none
  requireType := false

partial def trLevel : Level → M Syntax
  | Level.«_» => `(level| _)
  | Level.nat n => Syntax.mkNumLit (toString n)
  | Level.add l n => do `(level| $(← trLevel l.kind) + $(Syntax.mkNumLit (toString n.kind)))
  | Level.imax ls => do `(level| imax $[$(← ls.mapM fun l => trLevel l.kind)]*)
  | Level.max ls => do `(level| max $[$(← ls.mapM fun l => trLevel l.kind)]*)
  | Level.param u => mkIdent u
  | Level.paren l => trLevel l.kind -- do `(level| ($(← trLevel l.kind)))

partial def trPrio : Expr → M Syntax
  | Expr.nat n => Syntax.mkNumLit (toString n)
  | Expr.paren e => trPrio e.kind -- do `(prio| ($(← trPrio e.kind)))
  | _ => throw! "unsupported"

partial def trPrecExpr : Expr → M Syntax
  | Expr.nat n => Syntax.mkNumLit (toString n)
  | Expr.paren e => trPrecExpr e.kind -- do `(prec| ($(← trPrecExpr e.kind)))
  | _ => throw! "unsupported"

partial def trPrec : Precedence → M Syntax
  | Precedence.nat n => Syntax.mkNumLit (toString n)
  | Precedence.expr e => trPrecExpr e.kind

def trBinderName : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkHole arbitrary

def trBinderIdent : BinderName → Syntax
  | BinderName.ident n => mkNode ``binderIdent #[mkIdent n]
  | BinderName.«_» => mkNode ``binderIdent #[mkAtom "_"]

inductive TacticContext | seq | one

def optTy (ty : Option Syntax) : M (Option Syntax) :=
  ty.mapM fun stx => do `(Parser.Term.typeSpec| : $stx)

mutual

  partial def trBinderDefault (allowTac := true) : Default → M Syntax
    | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e.kind))
    | Default.«.» e => do
      unless allowTac do throw! "unsupported"
      `(Parser.Term.binderTactic| := by $(← trTactic $ Tactic.expr $ e.map Expr.ident))

  partial def trDArrow (bis : Array (Spanned Binder)) (ty : Expr) : M Syntax := do
    let bis ← trBinders { requireType := true } bis
    pure $ bis.foldr (init := ← trExpr ty) fun bi ty =>
      mkNode ``Parser.Term.depArrow #[bi, mkAtom "→", ty]

  partial def trBinder : BinderContext → Binder → Array Syntax → M (Array Syntax)
    | _, Binder.binder BinderInfo.instImplicit vars _ (some ty) none, out => do
      let var ← match vars with
      | none => #[]
      | some #[v] => pure #[trBinderName v.kind, mkAtom ":"]
      | some _ => throw! "unsupported (impossible)"
      out.push $ mkNode ``Parser.Term.instBinder
        #[mkAtom "[", mkNullNode var, ← trExpr ty.kind, mkAtom "]"]
    | ⟨allowSimp, req⟩, Binder.binder bi (some vars) bis ty dflt, out => do
      let ty := match req || !bis.isEmpty, ty with
      | true, none => some Expr.«_»
      | _, _ => ty.map (·.kind)
      let ty ← ty.mapM (trDArrow bis)
      let vars := mkNullNode $ vars.map fun v => trBinderName v.kind
      if let some stx ← trSimple allowSimp bi vars ty dflt then return out.push stx
      let ty := @mkNullNode $ match ty with | none => #[] | some ty => #[mkAtom ":", ty]
      if bi == BinderInfo.implicit then
        out.push $ mkNode ``Parser.Term.implicitBinder #[mkAtom "{", vars, ty, mkAtom "}"]
      else
        let dflt ← mkOptionalNode <$> dflt.mapM trBinderDefault
        out.push $ mkNode ``Parser.Term.explicitBinder #[mkAtom "(", vars, ty, dflt, mkAtom ")"]
    | _, _, _ => throw! "unsupported"
  where
    trSimple
    | some b, BinderInfo.default, vars, ty, none => do
      if b && ty.isSome then return none
      mkNode ``Parser.Term.simpleBinder #[vars, mkOptionalNode (← optTy ty)]
    | _, _, _, _, _ => none

  partial def trBinders (bc : BinderContext) (bis : Array (Spanned Binder)) : M (Array Syntax) := do
    bis.foldlM (fun out bi => trBinder bc bi.kind out) #[]

  partial def trExplicitBinders : Array (Spanned Binder) → M Syntax
    | #[⟨_, _, Binder.binder _ (some vars) _ ty none⟩] => do
      let ty ← match ty with | none => #[] | some ty => do #[mkAtom ":", ← trExpr ty.kind]
      mkNode ``explicitBinders #[mkNode ``unbracktedExplicitBinders #[
        mkNullNode $ vars.map fun n => trBinderIdent n.kind, mkNullNode ty]]
    | bis => do
      let bis ← bis.mapM fun
      | ⟨_, _, Binder.binder _ (some vars) _ ty none⟩ => do
        let vars ← vars.mapM fun n => trBinderIdent n.kind
        let ty ← match ty with | none => `(_) | some ty => trExpr ty.kind
        mkNode ``bracketedExplicitBinders #[mkAtom "(", mkNullNode vars, mkAtom ":", ty, mkAtom ")"]
      | _ => throw! "unsupported"
      mkNode ``explicitBinders #[mkNullNode bis]

  partial def trLambdaBinder : LambdaBinder → Array Syntax → M (Array Syntax)
    | LambdaBinder.reg bi, out => trBinder { allowSimple := some false } bi out
    | LambdaBinder.«⟨⟩» args, out => do out.push $ ← trExpr (Expr.«⟨⟩» args)

  partial def trLetDecl : LetDecl → M Syntax
    | LetDecl.var x bis ty val => do
      let letId := mkNode ``Parser.Term.letIdDecl #[
        trBinderName x.kind,
        mkNullNode $ ← trBinders { allowSimple := some true } bis,
        mkOptionalNode $ ← trOptType $ ty.map (·.kind),
        mkAtom ":=", ← trExpr val.kind]
      `(Parser.Term.letDecl| $letId:letIdDecl)
    | LetDecl.pat lhs val => do
      `(Parser.Term.letDecl| $(← trExpr lhs.kind):term := $(← trExpr val.kind))
    | LetDecl.notation n => throw! "unsupported"

  partial def trExpr : Expr → M Syntax
    | Expr.«...» => `(Parser.Term.calcDots| ...)
    | Expr.sorry => `(sorry)
    | Expr.«_» => `(_)
    | Expr.«()» => `(())
    | Expr.«{}» => `({})
    | Expr.ident n => mkIdent n
    | Expr.const _ n none => mkIdent n.kind
    | Expr.const _ n (some #[]) => mkIdent n.kind
    | Expr.const _ n (some l) => do
      mkNode ``Parser.Term.explicitUniv #[mkIdent n.kind,
        mkAtom ".{", (mkAtom ",").mkSep $ ← l.mapM fun e => trLevel e.kind, mkAtom "}"]
    | Expr.nat n => Syntax.mkNumLit (toString n)
    | Expr.decimal n d => (scientificLitOfDecimal n d).get!
    | Expr.string s => Syntax.mkStrLit s
    | Expr.char c => Syntax.mkCharLit c
    | Expr.paren e => trExpr e.kind -- do `(($(← trExpr e.kind)))
    | Expr.sort ty st u => do
      match ty, if st then some Level._ else u.map Spanned.kind with
      | false, none => `(Sort)
      | false, some u => do `(Sort $(← trLevel u))
      | true, none => `(Type)
      | true, some u => do `(Type $(← trLevel u))
    | Expr.«→» lhs rhs => do `($(← trExpr lhs.kind) → $(← trExpr rhs.kind))
    | Expr.fun true #[⟨_, _, LambdaBinder.reg (Binder.binder _ none _ (some ty) _)⟩] e => do
      `(fun $(mkIdent `this):ident: $(← trExpr ty.kind) => $(← trExpr e.kind))
    | Expr.fun _ bis e => do
      let bis ← bis.foldlM (fun out bi => trLambdaBinder bi.kind out) #[]
      `(fun $[$bis]* => $(← trExpr e.kind))
    | Expr.Pi bis e => do
      let dArrowHeuristic := !bis.any fun | ⟨_, _, Binder.binder _ _ _ none _⟩ => true | _ => false
      if dArrowHeuristic then trDArrow bis e.kind else
        `(∀ $[$(← trBinders { allowSimple := some false } bis)]*, $(← trExpr e.kind))
    | e@(Expr.app _ _) => do
      let rec appArgs : Expr → M (Syntax × Array Syntax)
      | Expr.app f x => do let (f, args) ← appArgs f.kind; (f, args.push (← trExpr x.kind))
      | e => do (← trExpr e, #[])
      let (f, args) ← appArgs e
      mkNode ``Parser.Term.app #[f, mkNullNode args]
    | Expr.show t pr => do
      mkNode ``Parser.Term.show #[mkAtom "show", ← trExpr t.kind, ← trProof pr.kind]
    | Expr.have true h t pr e => do
      let decl := mkNode ``Parser.Term.sufficesDecl #[
        mkOptionalNode $ h.map fun h => mkIdent h.kind, ← trExpr t.kind, ← trProof pr.kind]
      mkNode ``Parser.Term.suffices #[mkAtom "suffices", decl, mkNullNode, ← trExpr e.kind]
    | Expr.have false h t pr e => do
      let t := match t.kind with | Expr._ => none | t => some t
      let haveId := mkNode ``Parser.Term.haveIdDecl #[
        mkNullNode $ match h with | none => #[] | some h => #[mkIdent h.kind, mkNullNode],
        mkOptionalNode $ ← trOptType t, mkAtom ":=", ← trProof pr.kind false]
      mkNode ``Parser.Term.have #[mkAtom "have",
        mkNode ``Parser.Term.haveDecl #[haveId], mkNullNode, ← trExpr e.kind]
    | Expr.«.» _ e pr => do
      let pr ← match pr.kind with
      | Lean3.Proj.ident e => mkIdent e
      | Lean3.Proj.nat n => Syntax.mkLit fieldIdxKind (toString n)
      mkNode ``Parser.Term.proj #[← trExpr e.kind, mkAtom ".", pr]
    | Expr.if none c t e => do
      `(if $(← trExpr c.kind) then $(← trExpr t.kind) else $(← trExpr e.kind))
    | Expr.if (some h) c t e => do
      `(if $(mkIdent h.kind):ident : $(← trExpr c.kind)
        then $(← trExpr t.kind) else $(← trExpr e.kind))
    | Expr.calc args => do
      let (lhs, rhs) := args[0]
      mkNode ``Parser.Term.calc #[mkAtom "calc",
        ← trExpr lhs.kind, mkAtom ":", ← trExpr rhs.kind,
        mkNullNode $ ← args[1:].toArray.mapM fun (lhs, rhs) => do
          mkNullNode #[← trExpr lhs.kind, mkAtom ":", ← trExpr rhs.kind]]
    | Expr.«@» _ e => do `(@$(← trExpr e.kind))
    | Expr.pattern e => trExpr e.kind
    | Expr.«`()» lazy expr e => throw! "unsupported (TODO)"
    | Expr.«%%» e => throw! "unsupported (TODO)"
    | Expr.«`[]» tacs => throw! "unsupported (TODO)"
    | Expr.«`» false n => `($(Syntax.mkNameLit s!"`{n}"):nameLit)
    | Expr.«`» true n => `(`$(Syntax.mkNameLit s!"`{n}"):nameLit)
    | Expr.«⟨⟩» es => do `(⟨$[$(← es.mapM fun e => trExpr e.kind)],*⟩)
    | Expr.infix_fn c e => throw! "unsupported (TODO)"
    | Expr.«(,)» es => do
      `(($(← trExpr es[0].kind):term, $[$(← es[1:].toArray.mapM fun e => trExpr e.kind)],*))
    | Expr.«.()» e => trExpr e.kind
    | Expr.«:» e ty => do `(($(← trExpr e.kind) : $(← trExpr ty.kind)))
    | Expr.hole es => throw! "unsupported"
    | Expr.«#[]» es => throw! "unsupported"
    | Expr.by tac => do `(by $(← trTactic tac.kind))
    | Expr.begin tacs => do `(by $(← trBlock tacs))
    | Expr.let bis e => do
      bis.foldrM (init := ← trExpr e.kind) fun bi stx => do
        `(let $(← trLetDecl bi.kind):letDecl $stx)
    | Expr.match #[x] _ #[] => do `(nomatch $(← trExpr x.kind))
    | Expr.match xs _ #[] => do `(match $[$(← xs.mapM fun x => trExpr x.kind):term],* with.)
    | Expr.match xs ty eqns => do
      `(match $[$(← xs.mapM fun x => trExpr x.kind):term],* with $[$(← eqns.mapM trArm):matchAlt]*)
    | Expr.do _ els => do let els ← els.mapM fun e => trDoElem e.kind; `(do $[$els:doElem]*)
    | Expr.«{,}» es => do `({$[$(← es.mapM fun e => trExpr e.kind)],*})
    | Expr.subtype false x ty p => do
      `({$(mkIdent x.kind) $[: $(← trOptType (ty.map (·.kind)))]? // $(← trExpr p.kind)})
    | Expr.subtype true x ty p => do
      `({$(mkIdent x.kind) $[: $(← trOptType (ty.map (·.kind)))]? | $(← trExpr p.kind)})
    | Expr.sep x ty p => do
      `({$(mkIdent x.kind) ∈ $(← trExpr ty.kind) | $(← trExpr p.kind)})
    | Expr.setReplacement e bis => do
      `({$(← trExpr e.kind) | $[$(← trBinders {} bis):bracketedBinder]*})
    | Expr.structInst _ src flds #[] catchall => do
      let src ← src.mapM fun s => trExpr s.kind
      let flds ← flds.mapM fun (⟨_, _, lhs⟩, ⟨_, _, rhs⟩) => do
        if (match rhs with | Expr.ident rhs => rhs == lhs | _ => false : Bool) then
          `(Parser.Term.structInstFieldAbbrev| $(mkIdent lhs):ident)
        else
          `(Parser.Term.structInstField| $(mkIdent lhs):ident := $(← trExpr rhs))
      let catchall := mkOptionalNode $ if catchall then some (mkAtom "..") else none
      `({ $[$src with]? $[$flds:structInstField]* $catchall:optEllipsis })
    | Expr.structInst S src flds srcs catchall => throw! "unsupported (TODO)"
    | Expr.atPat lhs rhs => do `($(mkIdent lhs.kind)@ $(← trExpr rhs.kind))
    | Expr.notation n args => trNotation n args
    | Expr.userNotation n args => throw! "unsupported user notation {n}"

  partial def trOptType (ty : Option Expr) : M (Option Syntax) := ty.mapM trExpr >>= optTy

  partial def trArm : Arm → M Syntax
    | ⟨lhs, rhs⟩ => do
      `(Parser.Term.matchAltExpr|
        | $[$(← lhs.mapM fun e => trExpr e.kind)],* => $(← trExpr rhs.kind))

  partial def trDoElem : DoElem → M Syntax
    | DoElem.let decl => do `(doElem| let $(← trLetDecl decl.kind))
    | DoElem.eval e => do `(doElem| $(← trExpr e.kind):term)
    | DoElem.«←» lhs ty rhs els => do
      let rhs ← trExpr rhs.kind
      match lhs.kind.unparen, els with
      | Expr.ident lhs, none =>
        `(doElem| let $(mkIdent lhs):ident $[$(← trOptType (ty.map (·.kind)))]? ← $rhs:term)
      | _, _ =>
        let els ← els.mapM fun e => trExpr e.kind
        `(doElem| let $(← trExpr lhs.kind):term ← $rhs:term $[| $els:term]?)

  partial def trProof : Proof → (useFrom : Bool := true) → M Syntax
    | Proof.«from» _ e, useFrom => do
      let e ← trExpr e.kind
      if useFrom then `(Parser.Term.fromTerm| from $e) else e
    | Proof.block bl, _ => do `(by $(← trBlock bl))
    | Proof.by tac, _ => do `(by $(← trTactic tac.kind TacticContext.seq))

  partial def trBlock : Block → (c :_:= TacticContext.seq) → M Syntax
    | ⟨_, none, none, #[]⟩, TacticContext.seq => do `(Parser.Tactic.tacticSeqBracketed| {})
    | ⟨_, none, none, tacs⟩, TacticContext.seq =>
      mkNode ``Parser.Tactic.tacticSeq1Indented <$> tacs.mapM fun tac => do
        mkGroupNode #[← trTactic tac.kind, mkNullNode]
    | ⟨_, cl, cfg, tacs⟩, TacticContext.one => throw! "unsupported (TODO)"
    | ⟨_, cl, cfg, tacs⟩, _ => throw! "unsupported (TODO)"

  partial def trTactic : Tactic → (c :_:= TacticContext.one) → M Syntax
    | Tactic.block bl, c => trBlock bl c
    | Tactic.by tac, c => trBlock ⟨true, none, none, #[tac]⟩ c
    | tac, TacticContext.seq => do
      mkNode ``Parser.Tactic.tacticSeq1Indented #[mkGroupNode #[← trTactic tac, mkNullNode]]
    | Tactic.«;» tacs, TacticContext.one => do
      let rec build (i : Nat) (lhs : Syntax) : M Syntax :=
        if h : i < tacs.size then do
          match ← trTacticOrList (tacs.get ⟨i, h⟩).kind with
          | Sum.inl tac => `(tactic| $lhs <;> $(← build (i+1) tac))
          | Sum.inr tacs => build (i+1) (← `(tactic| $lhs <;> [$[$tacs],*]))
        else lhs
      build 1 (← trTactic tacs[0].kind)
    | Tactic.«<|>» tacs, TacticContext.one => do
      let tacs ← tacs.mapM fun tac => trTactic tac.kind
      `(tactic| first $[| $tacs]*)
    | Tactic.«[]» tacs, _ => throw! "unsupported (impossible)"
    | Tactic.exact_shortcut e, TacticContext.one => do `(tactic| exact $(← trExpr e.kind))
    | Tactic.expr e, TacticContext.one => do
      match ← trExpr e.kind with
      | `(do $[$els]*) => `(tactic| do $[$els:doElem]*)
      | stx => `(tactic| do $stx:term)
    | Tactic.interactive n args, TacticContext.one => throw! "unsupported tactic {repr n}"

  partial def trTacticOrList : Tactic → M (Sum Syntax (Array Syntax))
    | Tactic.«[]» args => Sum.inr <$> args.mapM fun arg => trTactic arg.kind
    | tac => Sum.inl <$> trTactic tac

  partial def trNotation (n : Choice) (args : Array (Spanned Arg)) : M Syntax := do
    let n ← match n with
    | Choice.one n => n
    | Choice.many ns => if ns[1:].all (ns[0] == ·) then ns[0] else throw! "unsupported"
    match (← get).notations.find? n.getString!, args.map (·.kind) with
    | some ⟨NotationKind.const stx, _⟩, #[] => stx
    | some ⟨NotationKind.const stx, _⟩, _ => throw! "unsupported (impossible)"
    | some ⟨NotationKind.unary f, _⟩, #[Arg.expr e] => f (← trExpr e)
    | some ⟨NotationKind.unary f, _⟩, _ => throw! "unsupported (impossible)"
    | some ⟨NotationKind.binary f, _⟩, #[Arg.expr e₁, Arg.expr e₂] => f (← trExpr e₁) (← trExpr e₂)
    | some ⟨NotationKind.binary f, _⟩, _ => throw! "unsupported (impossible)"
    | some ⟨NotationKind.nary f, _⟩, args =>
      f <$> args.mapM fun | Arg.expr e => trExpr e | _ => throw! "unsupported (impossible)"
    | some ⟨NotationKind.exprs f, _⟩, #[Arg.exprs es] => f $ ← es.mapM fun e => trExpr e.kind
    | some ⟨NotationKind.exprs f, _⟩, _ => throw! "unsupported (impossible)"
    | some ⟨NotationKind.binder f, _⟩, #[Arg.binder bi, Arg.expr e] => do
      f (← trExplicitBinders #[Spanned.dummy bi]) (← trExpr e)
    | some ⟨NotationKind.binder f, _⟩, #[Arg.binders bis, Arg.expr e] => do
      if bis.isEmpty then trExpr e else f (← trExplicitBinders bis) (← trExpr e)
    | some ⟨NotationKind.binder f, _⟩, _ => throw! "unsupported (impossible)"
    | some ⟨NotationKind.fail, _⟩, args =>
      dbg_trace "unsupported notation {repr n}"
      let args ← args.mapM fun | Arg.expr e => trExpr e | _ => throw! "unsupported notation {repr n}"
      mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]
    | none, args =>
      dbg_trace "unsupported notation {repr n}"
      let args ← args.mapM fun | Arg.expr e => trExpr e | _ => throw! "unsupported notation {repr n}"
      mkNode ``Parser.Term.app #[mkIdent n, mkNullNode args]

end

inductive TrAttr
  | del : Syntax → TrAttr
  | add : Syntax → TrAttr
  | prio : Expr → TrAttr
  | parsingOnly : TrAttr
  | unify : TrAttr

def trAttr (prio : Option Expr) : Attribute → M (Option TrAttr)
  | Attribute.priority n => TrAttr.prio n.kind
  | Attribute.del n => do
    let n ← match n with
    | `instance => `instance
    | `simp => `simp
    | `congr => `congr
    | `inline => `inline
    | `pattern => `matchPattern
    | _ => throw! "unsupported attr -{n}"
    TrAttr.del (← `(Parser.Command.eraseAttr| -$(mkIdent n)))
  | AST3.Attribute.add `parsing_only none => TrAttr.parsingOnly
  | AST3.Attribute.add `unify none => TrAttr.unify
  | AST3.Attribute.add n arg => do
    let mkSimpleAttr n (args := #[]) := mkNode ``Parser.Attr.simple #[mkIdent n, mkNullNode args]
    let attr ← match n, arg with
    | `class,         none => `(attr| class)
    | `instance,      none => `(attr| instance)
    | `simp,          none => `(attr| simp)
    | `recursor,      some ⟨_, _, AttrArg.indices #[]⟩ => throw! "unsupported"
    | `recursor,      some ⟨_, _, AttrArg.indices #[⟨_, _, n⟩]⟩ =>
      `(attr| recursor $(Syntax.mkNumLit (toString n)):numLit)
    | `congr,         none => mkSimpleAttr `congr
    | `inline,        none => mkSimpleAttr `inline
    | `pattern,       none => mkSimpleAttr `matchPattern
    | `reducible,     none => mkSimpleAttr `reducible
    | `semireducible, none => mkSimpleAttr `semireducible
    | `irreducible,   none => mkSimpleAttr `irreducible
    | `elab_simple,   none => mkSimpleAttr `elabWithoutExpectedType
    | `vm_override,   some ⟨_, _, AttrArg.vmOverride n none⟩ =>
      mkSimpleAttr `implementedBy #[mkIdent n.kind]
    | _, _ =>
      if builtinAttributes.contains n then
        dbg_trace "suppressing unsupported attr {n}"
        return none
      else if (← get).simpSets.contains n then
        dbg_trace "suppressing simp set attr {n}"
        return none
      else
        throw! "unknown attr {n}"
    TrAttr.add attr

def trAttrKind : AttributeKind → M Syntax
  | AttributeKind.global => `(Parser.Term.attrKind|)
  | AttributeKind.scoped => `(Parser.Term.attrKind| scoped)
  | AttributeKind.local => `(Parser.Term.attrKind| local)

structure SpecialAttrs where
  prio : Option AST3.Expr := none
  parsingOnly := false
  unify := false

def AttrState := SpecialAttrs × Array Syntax

def trAttrInstance (attr : Attribute) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit := do
  match ← trAttr (← get).1.prio attr with
  | some (TrAttr.del stx) => do
    unless allowDel do throw! "unsupported (impossible)"
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.add stx) => do
    let stx := mkNode ``Parser.Term.attrInstance #[← trAttrKind kind, stx]
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.prio prio) => modify fun s => { s with 1.prio := prio }
  | some TrAttr.parsingOnly => modify fun s => { s with 1.parsingOnly := true }
  | some TrAttr.unify => modify fun s => { s with 1.unify := true }
  | none => pure ()

def trAttributes (attrs : Attributes) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit :=
  attrs.forM fun attr => trAttrInstance attr.kind allowDel kind

structure Modifiers4 where
  docComment : Option String := none
  attrs : AttrState := ({}, #[])
  vis : Visibility := Visibility.regular
  «noncomputable» : Option Unit := none
  safety : DefinitionSafety := DefinitionSafety.safe

def mkOpt (a : Option α) (f : α → M Syntax) : M Syntax :=
  match a with
  | none => mkNullNode
  | some a => do mkNullNode #[← f a]

def trModifiers (mods : Modifiers) : M (SpecialAttrs × Syntax) :=
  mods.foldlM trModifier {} >>= toSyntax
where
  trModifier (s : Modifiers4) (m : Spanned Modifier) : M Modifiers4 :=
    match m.kind with
    | Modifier.private => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.private }
      | _ => throw! "unsupported (impossible)"
    | Modifier.protected => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.protected }
      | _ => throw! "unsupported (impossible)"
    | Modifier.noncomputable => match s.noncomputable with
      | none => pure { s with «noncomputable» := some () }
      | _ => throw! "unsupported (impossible)"
    | Modifier.meta => match s.safety with
      | DefinitionSafety.safe => pure { s with safety := DefinitionSafety.unsafe }
      | _ => throw! "unsupported (impossible)"
    | Modifier.mutual => s -- mutual is duplicated elsewhere in the grammar
    | Modifier.attr loc _ attrs => do
      let kind := if loc then AttributeKind.local else AttributeKind.global
      pure { s with attrs := (← trAttributes attrs false kind |>.run ({}, #[])).2 }
    | Modifier.doc doc => match s.docComment with
      | none => pure { s with docComment := some doc }
      | _ => throw! "unsupported (impossible)"
  toSyntax : Modifiers4 → M (SpecialAttrs × Syntax)
  | ⟨doc, (s, attrs), vis, nc, safety⟩ => do
    let doc := mkOptionalNode $ doc.map trDocComment
    let attrs ← mkOpt (if attrs.isEmpty then none else some attrs) fun attrs =>
      `(Parser.Term.attributes| @[$[$attrs],*])
    let vis := mkOptionalNode $ ← match vis with
    | Visibility.regular => none
    | Visibility.private => `(Parser.Command.visibility| private)
    | Visibility.protected => `(Parser.Command.visibility| protected)
    let nc ← mkOpt nc fun () => `(Parser.Command.noncomputable| noncomputable)
    let part := mkOptionalNode $ ← match safety with
    | DefinitionSafety.partial => some <$> `(Parser.Command.partial| partial)
    | _ => none
    let uns := mkOptionalNode $ ← match safety with
    | DefinitionSafety.unsafe => some <$> `(Parser.Command.unsafe| unsafe)
    | _ => none
    (s, mkNode ``Parser.Command.declModifiers #[doc, attrs, vis, nc, part, uns])

def trOpenCmd (ops : Array Open) : M Unit := do
  let mut simple := #[]
  let pushSimple (s : Array Syntax) := unless s.isEmpty do pushM `(command| open $[$s]*)
  for o in ops do
    match o with
    | ⟨tgt, none, clauses⟩ =>
      if clauses.isEmpty then
        simple := simple.push (mkIdent tgt.kind)
      else
        pushSimple simple; simple := #[]
        let mut explicit := #[]
        let mut renames := #[]
        let mut hides := #[]
        for c in clauses do
          match c.kind with
          | OpenClause.explicit ns => explicit := explicit ++ ns
          | OpenClause.renaming ns => renames := renames ++ ns
          | OpenClause.hiding ns => hides := hides ++ ns
        match explicit.isEmpty, renames.isEmpty, hides.isEmpty with
        | true, true, true => pure ()
        | false, true, true =>
          let ns := explicit.map fun n => mkIdent n.kind
          pushM `(command| open $(mkIdent tgt.kind):ident ($[$ns]*))
        | true, false, true =>
          let rs ← renames.mapM fun ⟨a, b⟩ =>
            `(Parser.Command.openRenamingItem|
              $(mkIdent a.kind):ident → $(mkIdent b.kind):ident)
          pushM `(command| open $(mkIdent tgt.kind):ident renaming $[$rs],*)
        | true, true, false =>
          let ns := hides.map fun n => mkIdent n.kind
          pushM `(command| open $(mkIdent tgt.kind):ident hiding $[$ns]*)
        | _, _, _ => throw! "unsupported"
    | _ => throw! "unsupported"
  pushSimple simple

def trExportCmd : Open → M Unit
  | ⟨tgt, none, clauses⟩ => do
    let mut args := #[]
    for c in clauses do
      match c.kind with
      | OpenClause.explicit ns =>
        for n in ns do args := args.push (mkIdent n.kind)
      | _ => throw! "unsupported"
    pushM `(export $(mkIdent tgt.kind):ident ($[$args]*))
  | _ => throw! "unsupported"

def trDeclId (n : Name) (us : LevelDecl) : M Syntax := do
  let us := us.map $ Array.map fun u => mkIdent u.kind
  `(Parser.Command.declId| $(mkIdent n):ident $[.{$[$us],*}]?)

def trDeclSig (req : Bool) (bis : Binders) (ty : Option (Spanned Expr)) : M Syntax := do
  let bis := mkNullNode (← trBinders { allowSimple := some true } bis)
  let ty := ty.map Spanned.kind
  let ty ← trOptType $ if req then some (ty.getD Expr.«_») else ty
  if req then mkNode ``Parser.Command.declSig #[bis, ty.get!]
  else mkNode ``Parser.Command.optDeclSig #[bis, mkOptionalNode ty]

def trAxiom (mods : Modifiers) (n : Name)
  (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr)) : M Unit := do
  let (_, mods) ← trModifiers mods
  pushM `(command| $mods:declModifiers axiom $(← trDeclId n us) $(← trDeclSig true bis ty))

def trDecl (dk : DeclKind) (mods : Modifiers) (n : Option (Spanned Name)) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr)) (val : DeclVal) : M (Option Syntax) := do
  let (s, mods) ← trModifiers mods
  if s.unify then return none
  let id ← n.mapM fun n => trDeclId n.kind us
  let sig req := trDeclSig req bis ty
  let val ← match val with
  | DeclVal.expr e => do `(Parser.Command.declValSimple| := $(← trExpr e))
  | DeclVal.eqns #[] => `(Parser.Command.declValSimple| := fun.)
  | DeclVal.eqns arms => do `(Parser.Command.declValEqns| $[$(← arms.mapM trArm):matchAlt]*)
  match dk with
  | DeclKind.abbrev => do `(command| $mods:declModifiers abbrev $id.get! $(← sig false) $val)
  | DeclKind.def => do `(command| $mods:declModifiers def $id.get! $(← sig false) $val)
  | DeclKind.example => do `(command| $mods:declModifiers example $(← sig true) $val)
  | DeclKind.theorem => do `(command| $mods:declModifiers theorem $id.get! $(← sig true) $val)
  | DeclKind.instance => do
    let prio ← s.prio.mapM fun prio => do
      `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
    `(command| $mods:declModifiers instance $[$prio:namedPrio]? $[$id:declId]? $(← sig true) $val)

def trInferKind : Option InferKind → M (Option Syntax)
  | some InferKind.implicit => `(Parser.Command.inferMod | {})
  | some InferKind.relaxedImplicit => `(Parser.Command.inferMod | {})
  | some InferKind.none => none
  | none => none

def trInductive (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (ty : Option (Spanned Expr))
  (nota : Option Notation) (intros : Array (Spanned Intro)) : M Syntax := do
  let (prio, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let sig ← trDeclSig false bis ty
  let ctors ← intros.mapM fun ⟨_, _, ⟨doc, name, ik, bis, ty⟩⟩ => do
    `(Parser.Command.ctor| |
      $[$(doc.map trDocComment):docComment]?
      $(mkIdent name.kind):ident
      $[$(← trInferKind ik):inferMod]?
      $(← trDeclSig false bis ty):optDeclSig)
  if cl then
    `(command| $mods:declModifiers class inductive $id:declId $sig:optDeclSig $[$ctors:ctor]*)
  else
    `(command| $mods:declModifiers inductive $id:declId $sig:optDeclSig $[$ctors:ctor]*)

def trMutual (decls : Array (Mutual α)) (f : Mutual α → M Syntax) : M Unit := do
  pushM `(mutual $[$(← decls.mapM f)]* end)

def trField : Field → Array Syntax → M (Array Syntax)
  | Field.binder bi ns ik bis ty dflt, out => do
    let ns := ns.map fun n => mkIdent n.kind
    let im ← trInferKind ik
    let sig req := trDeclSig req bis ty
    out.push <$> match bi with
    | BinderInfo.implicit => do
      `(Parser.Command.structImplicitBinder| {$[$ns]* $[$im]? $(← sig true):declSig})
    | BinderInfo.instImplicit => do
      `(Parser.Command.structInstBinder| [$[$ns]* $[$im]? $(← sig true):declSig])
    | _ => do
      let sig ← sig false
      let dflt ← dflt.mapM (trBinderDefault false)
      if ns.size = 1 then
        `(Parser.Command.structSimpleBinder| $(ns[0]):ident $[$im]? $sig:optDeclSig $[$dflt]?)
      else
        `(Parser.Command.structExplicitBinder| ($[$ns]* $[$im]? $sig:optDeclSig $[$dflt]?))
  | Field.notation _, out => throw! "unsupported"

def trFields (flds : Array (Spanned Field)) : M Syntax := do
  let flds ← flds.foldlM (fun out fld => trField fld.kind out) #[]
  mkNode ``Parser.Command.structFields #[mkNullNode flds]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let (prio, mods) ← trModifiers mods
  let id ← trDeclId n.kind us
  let bis := mkNullNode $ ← trBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, _, false, none, ty, #[]⟩ => trExpr ty.kind
    | _ => throw! "unsupported"
  let exts ← mkOpt (if exts.isEmpty then none else some exts) fun exts =>
    `(Parser.Command.extends| extends $[$exts],*)
  let ty ← mkOptionalNode <$> trOptType (ty.map Spanned.kind)
  let flds ← @mkNullNode <$> match mk, flds with
  | none, #[] => #[]
  | mk, flds => do
    let mk ← mk.mapM fun ⟨_, _, n, ik⟩ => do
      `(Parser.Command.structCtor| $(mkIdent n.kind):ident $[$(← trInferKind ik)]? ::)
    #[mkAtom "where", mkOptionalNode mk, ← trFields flds]
  let decl := mkNode ``Parser.Command.structure #[
    ← if cl then `(Parser.Command.classTk| class) else `(Parser.Command.structureTk| structure),
    id, bis, exts, ty, flds, ← `(Parser.Command.optDeriving|)]
  pushM `(command| $mods:declModifiers $decl:structure)

def trNotationCmd (loc : LocalReserve) (attrs : Attributes) (nota : Notation) : M Unit := do
  let (s, attrs) := (← trAttributes attrs false AttributeKind.global |>.run ({}, #[])).2
  unless attrs.isEmpty do throw! "unsupported (impossible)"
  if loc.2 then return
  let kind ← if loc.1 then `(Parser.Term.attrKind| local) else `(Parser.Term.attrKind|)
  let n := nota.name3
  let skip : Bool := match (← get).notations.find? n with
  | some ⟨_, skip⟩ => skip
  | none => false
  if skip && !loc.1 then return
  let prio ← s.prio.mapM fun prio => do
    `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
  let mut new := NotationKind.fail
  let n4 := nota.name4
  -- FIXME, this is wrong but lets the parenthesizer work on local notations
  let fakeNode as := mkNode ``Parser.Term.app #[mkIdent n4, mkNullNode as]
  let cmd ← match nota with
  | Notation.mixfix m (tk, prec) (some e) =>
    let p ← prec.mapM fun p => trPrec p.kind
    let tk := tk.kind.toString
    let s := Syntax.mkStrLit tk
    let e ← trExpr e.kind
    match m with
    | MixfixKind.infix =>
      -- new := NotationKind.binary fun a b => mkNode n4 #[a, mkAtom tk, b]
      new := NotationKind.binary fun a b => fakeNode #[a, b]
      `(command| $kind:attrKind infixl$[:$p]? $[$prio:namedPrio]? $s => $e)
    | MixfixKind.infixl =>
      -- new := NotationKind.binary fun a b => mkNode n4 #[a, mkAtom tk, b]
      new := NotationKind.binary fun a b => fakeNode #[a, b]
      `(command| $kind:attrKind infixl$[:$p]? $[$prio:namedPrio]? $s => $e)
    | MixfixKind.infixr =>
      -- new := NotationKind.binary fun a b => mkNode n4 #[a, mkAtom tk, b]
      new := NotationKind.binary fun a b => fakeNode #[a, b]
      `(command| $kind:attrKind infixr$[:$p]? $[$prio:namedPrio]? $s => $e)
    | MixfixKind.prefix =>
      -- new := NotationKind.unary fun a => mkNode n4 #[mkAtom tk, a]
      new := NotationKind.unary fun a => fakeNode #[a]
      `(command| $kind:attrKind prefix$[:$p]? $[$prio:namedPrio]? $s => $e)
    | MixfixKind.postfix =>
      -- new := NotationKind.unary fun a => mkNode n4 #[a, mkAtom tk]
      new := NotationKind.unary fun a => fakeNode #[a]
      `(command| $kind:attrKind postfix$[:$p]? $[$prio:namedPrio]? $s => $e)
  | Notation.notation lits (some e) =>
    let p ← match lits.get? 0 with
    | some ⟨_, _, Literal.sym tk⟩ => tk.2.mapM fun p => trPrec p.kind
    | some ⟨_, _, Literal.var _ _⟩ => match lits.get? 1 with
      | some ⟨_, _, Literal.sym tk⟩ => tk.2.mapM fun p => trPrec p.kind
      | _ => none
    | _ => none
    new := match lits with
    | #[⟨_, _, Literal.sym tk⟩] =>
      NotationKind.const (mkNode n4 #[mkAtom tk.1.kind.toString])
    | _ => match mkNAry lits with
      | some f =>
        -- NotationKind.nary fun stxs => mkNode n4 (f stxs).2
        NotationKind.nary @fakeNode
      | none => NotationKind.fail
    let lits ← lits.mapM fun
    | ⟨_, _, Literal.sym tk⟩ => Syntax.mkStrLit tk.1.kind.toString
    | ⟨_, _, Literal.var x none⟩ =>
      `(Parser.Command.identPrec| $(mkIdent x.kind):ident)
    | ⟨_, _, Literal.var x (some ⟨_, _, Action.prec p⟩)⟩ => do
      `(Parser.Command.identPrec| $(mkIdent x.kind):ident : $(← trPrec p))
    | _ => throw! "unsupported"
    let e ← trExpr e.kind
    `(command| $kind:attrKind notation$[:$p]? $[$prio:namedPrio]? $[$lits]* => $e)
  | _ => throw! "unsupported (impossible)"
  push cmd
  modify fun s => { s with notations := s.notations.insert n ⟨new, false⟩ }
where
  mkNAry (lits : Array (Spanned AST3.Literal)) :
    Option (Array Syntax → Nat × Array Syntax) :=
    lits.foldl (init := some fun stx => (0, #[])) fun
    | some f, ⟨_, _, Literal.sym tk⟩ =>
      let stx := mkAtom tk.1.kind.toString
      some fun as => let (i, bs) := f as; (i, bs.push stx)
    | some f, ⟨_, _, Literal.var _ _⟩ =>
      some fun as => let (i, bs) := f as; (i+1, bs.push (as.getD i Syntax.missing))
    | _, _ => none

def trCommand : Command → M Unit
  | Command.prelude => modify fun s => { s with «prelude» := true }
  | Command.initQuotient => pushM `(init_quot)
  | Command.«import» ns => modify fun s =>
    { s with imports := ns.foldl (fun a n => a.push n.kind) s.imports }
  | Command.mdoc doc =>
    push $ mkNode ``Parser.Command.modDocComment #[mkAtom "/!", mkAtom (doc ++ "-/")]
  | Command.«universe» _ _ ns =>
    pushM `(universe $[$(ns.map fun n => mkIdent n.kind)]*)
  | Command.«namespace» n => do
    pushScope; pushM `(namespace $(mkIdent n.kind))
  | Command.«section» n => do
    pushScope; pushM `(section $[$(n.map fun n => mkIdent n.kind)]?)
  | Command.«end» n => do
    popScope; pushM `(end $[$(n.map fun n => mkIdent n.kind)]?)
  | Command.«variable» vk _ _ bis =>
    unless bis.isEmpty do
      let bis ← trBinders {} bis
      match vk with
      | VariableKind.variable => pushM `(variable $[$bis]*)
      | VariableKind.parameter => pushM `(parameter $[$bis]*)
  | Command.axiom _ mods n us bis ty => trAxiom mods n.kind us bis ty
  | Command.axioms _ mods bis => bis.forM fun
    | ⟨_, _, Binder.binder _ (some ns) bis (some ty) none⟩ => ns.forM fun
      | ⟨_, _, BinderName.ident n⟩ => trAxiom mods n none bis ty
      | _ => throw! "unsupported (impossible)"
    | _ => throw! "unsupported (impossible)"
  | Command.decl dk mods n us bis ty val => do
    if let some decl ← trDecl dk mods n us bis ty val.kind then
      push decl
  | Command.mutualDecl dk mods us bis arms =>
    trMutual arms fun ⟨attrs, n, ty, vals⟩ => do
      match ← trDecl dk mods n us bis ty (DeclVal.eqns vals) with
      | none => throw! "unsupported"
      | some decl => decl
  | Command.inductive cl mods n us bis ty nota intros =>
     pushM $ trInductive cl mods n us bis ty nota intros
  | Command.mutualInductive cl mods us bis nota inds =>
    trMutual inds fun ⟨attrs, n, ty, intros⟩ => do
      trInductive cl mods n us bis ty nota intros
  | Command.structure cl mods n us bis exts ty m flds =>
    trStructure cl mods n us bis exts ty m flds
  | Command.attribute loc _ attrs ns => do
    let kind := if loc then AttributeKind.local else AttributeKind.global
    let attrs := (← trAttributes attrs true kind |>.run ({}, #[])).2.2
    if attrs.isEmpty || ns.isEmpty then return ()
    let ns := ns.map fun n => mkIdent n.kind
    pushM `(command| attribute [$[$attrs],*] $[$ns]*)
  | Command.precedence sym prec => pure ()
  | Command.notation loc attrs n => trNotationCmd loc attrs n
  | Command.open true ops => ops.forM trExportCmd
  | Command.open false ops => trOpenCmd ops
  | Command.include true ops => unless ops.isEmpty do
      pushM `(include $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.include false ops => unless ops.isEmpty do
      pushM `(omit $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.hide ops => unless ops.isEmpty do
      throw! "unsupported"
      -- pushM `(hide $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.theory #[⟨_, _, Modifier.noncomputable⟩] => pushM `(command| noncomputable theory)
  | Command.theory _ => throw! "unsupported (impossible)"
  | Command.setOption n val => match n.kind, val.kind with
    | `old_structure_cmd, OptionVal.bool b =>
      modifyScope fun s => { s with oldStructureCmd := b }
    | _, _ => throw! "unsupported (TODO)"
  | Command.declareTrace n => throw! "unsupported (TODO)"
  | Command.addKeyEquivalence a b => throw! "unsupported"
  | Command.runCmd e => do pushM `(#eval $(← trExpr e.kind))
  | Command.check e => do pushM `(#check $(← trExpr e.kind))
  | Command.reduce _ e => do pushM `(#reduce $(← trExpr e.kind))
  | Command.eval e => do pushM `(#eval $(← trExpr e.kind))
  | Command.unify e₁ e₂ => throw! "unsupported"
  | Command.compile n => throw! "unsupported"
  | Command.help n => throw! "unsupported"
  | Command.print (PrintCmd.str s) => pushM `(#print $(Syntax.mkStrLit s))
  | Command.print (PrintCmd.ident n) => pushM `(#print $(mkIdent n.kind))
  | Command.print (PrintCmd.axioms (some n)) => pushM `(#print axioms $(mkIdent n.kind))
  | Command.print _ => throw! "unsupported"
  | Command.userCommand n mods args => throw! "unsupported (TODO)"

def AST3toData4 : AST3 → M Data4
  | ⟨commands⟩ => do
    commands.forM fun c => trCommand c.kind
    let s ← get
    let header := mkNode ``Parser.Module.header #[
      mkOptionalNode $ match s.prelude with
      | true => some $ mkNode ``Parser.Module.prelude #[mkAtom "prelude"]
      | false => none,
      mkNullNode $ s.imports.map fun n =>
        mkNode ``Parser.Module.import #[mkAtom "import", mkNullNode, mkIdent n]]
    pure ⟨mkNode ``Parser.Module.module #[header, mkNullNode s.commands], HashMap.empty⟩

def M.run (m : M α) : Except String α := do
  match EStateM.run m {} with
  | EStateM.Result.ok a _ => a
  | EStateM.Result.error e _ => throw e

end Translate

def AST3toData4 (ast : AST3) : Except String Data4 := (Translate.AST3toData4 ast).run

-- open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
-- open Lean.Parser Lean.PrettyPrinter

-- set_option trace.PrettyPrinter.parenthesize true in
-- #eval show CoreM Unit from do
--   let s ← IO.FS.readFile "/home/mario/Documents/lean/lean/library/init/data/nat/lemmas.ast.json"
--   let json ← Json.parse s
--   let ⟨ast, commands, level, expr⟩ ← fromJson? json (α := Parse.RawAST3)
--   let level := Parse.buildLevels level
--   let expr := Parse.buildExprs level expr
--   for c in commands[0:] do
--     -- println! (repr (← Parse.getNode c |>.run ⟨ast, expr⟩)).group ++ "\n"
--     println! (repr (← Parse.getCommand c |>.run ⟨ast, expr⟩).kind).group ++ "\n"
--     let c ← Parse.getCommand c |>.run ⟨ast, expr⟩
--     let ⟨stx, _⟩ ← match AST3toData4 ⟨#[c]⟩ with
--     | Except.ok e => e
--     | Except.error e => throwError "{e}"
--     -- println! "{stx}\n\n"
--     let stx ← parenthesize Parser.Module.module.parenthesizer stx
--     -- println! "{stx}\n\n"
--     let fmt ← format Parser.Module.module.formatter stx
--     println! "{fmt}"

-- #eval show CoreM Unit from do
--   let ⟨ast⟩ ← parseAST3 "/home/mario/Documents/lean/lean/library/init/logic.ast.json"
--   let ⟨stx, _⟩ ← match AST3toData4 ⟨ast[290:292].toArray⟩ with
--   | Except.ok e => e
--   | Except.error e => throwError "{e}"
--   -- let stx := stx[1][0]
--   println! "{stx[1]}\n\n"
--   let stx ← parenthesize Parser.Module.module.parenthesizer stx
--   println! "{stx}\n\n"
--   let fmt ← format Parser.Module.module.formatter stx
--   println! "{fmt}"
