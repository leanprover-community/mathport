/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Syntax.Translate.Basic

namespace Mathport.Translate

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param
open AST3

def mkCDot : Term := Unhygienic.run `(·)

partial def scientificLitOfDecimal (num den : Nat) : Option (TSyntax scientificLitKind) :=
  findExp num den 0 |>.map fun (m, e) =>
    let str := toString m
    if e == str.length then
      Syntax.mkScientificLit ("0." ++ str)
    else if e < str.length then
      let mStr := str.extract 0 ⟨str.length - e⟩
      let eStr := str.extract ⟨str.length - e⟩ ⟨str.length⟩
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

def trExtendedBindersGrouped
  (reg : Array Syntax.SimpleOrBracketedBinder → Term → Term)
  (ext : TSyntax ``binderIdent → TSyntax `binderPred → Term → Term)
  (bc : BinderContext) (bis : Array Binder') (e : Spanned Expr) : M Term := do
  let tr1 : Array Syntax.SimpleOrBracketedBinder × (Term → Term) → Binder' →
      M (Array Syntax.SimpleOrBracketedBinder × (Term → Term))
    | (args, f), Binder'.basic stx => pure (args.push stx, f)
    | (args, f), bic@(Binder'.collection _bi vars n rhs) => do
      match vars, predefinedBinderPreds.find? n with
      | #[v], some g =>
        let v := trBinderIdent v.kind
        let pred := g (← trExpr rhs)
        pure (#[], fun e => f $ reg args $ ext v pred e)
      | _, _ => pure (args ++ (← expandBinder bc bic), f)
  let (args, f) ← bis.foldlM tr1 (#[], id)
  pure $ f $ reg args (← trExpr e)

def trExplicitBinders : Array (Spanned Binder) → M (TSyntax ``explicitBinders)
  | #[⟨_, Binder.binder _ (some vars) _ ty none⟩] => do
    let ty ← ty.mapM trExpr
    `(explicitBinders| $[$(vars.map (trBinderIdent ·.kind)):binderIdent]* $[: $ty]?)
  | bis => do
    let trBasicBinder (vars : Option (Array (Spanned BinderName)))
        (ty : Option (Spanned Expr)) : M (TSyntax ``bracketedExplicitBinders) := do
      let vars := match vars with
        | some vars => vars.map fun n => trBinderIdent n.kind
        | none => #[Id.run `(binderIdent| _)]
      let ty ← match ty with | none => `(_) | some ty => trExpr ty
      `(bracketedExplicitBinders| ($[$vars]* : $ty))
    let rec trBinder : AST3.Binder → M (Array (TSyntax ``bracketedExplicitBinders))
      | Binder.binder _ vars _ ty none => return #[← trBasicBinder vars ty]
      | Binder.collection bi vars n rhs =>
        expandBinderCollection (fun vars ty => return #[← trBasicBinder vars ty])
          bi vars n rhs
      | Binder.notation _ => warn! "unsupported: (notation) binder"
      | _ => warn! "unsupported (impossible)"
    let bis ← bis.concatMapM (spanning fun bi => trBinder bi)
    `(explicitBinders| $[$bis]*)

def trExplicitBindersExt
  (reg : TSyntax ``explicitBinders → Term → Term)
  (ext : Option (TSyntax ``binderIdent → TSyntax `binderPred → Term → Term))
  (bis : Array (Spanned Binder)) (e : Spanned Expr) : M Term := do
  let reg' (bis) : M (Term → Term) := do
    if bis.isEmpty then pure id else reg <$> trExplicitBinders bis
  match ext with
  | none => return (← reg' bis) (← trExpr e)
  | some ext => do
    let (left, f) ← bis.foldlM (init := (#[], id)) fun (left, f) bi => do
      if let Binder.collection _ #[v] n rhs := bi.kind then
        if let some g := predefinedBinderPreds.find? n then
          pure (#[], f ∘ (← reg' left) ∘ ext (trBinderIdent v.kind) (g (← trExpr rhs)))
        else pure (left.push bi, f)
      else pure (left.push bi, f)
    pure $ f ((← reg' left) (← trExpr e))

def trExtBinders (args : Array (Spanned Binder)) : M Syntax := do
  let out ← args.concatMapM fun
  | ⟨_, Binder.binder _ vars _ ty _⟩ =>
    trBasicBinder (vars.getD #[Spanned.dummy BinderName._]) ty
  | ⟨_, Binder.collection bi vars n rhs⟩ =>
    if let some g := predefinedBinderPreds.find? n then
      onVars vars fun v =>
        return #[← `(Std.ExtendedBinder.extBinder|
          $(trBinderIdent v):binderIdent $(g (← trExpr rhs)):binderPred)]
    else
      expandBinderCollection trBasicBinder bi vars n rhs
  | ⟨_, Binder.notation _⟩ => warn! "unsupported: (notation) binder" | pure #[]
  if let #[bi] := out then `(Std.ExtendedBinder.extBinders| $bi:extBinder)
  else `(Std.ExtendedBinder.extBinders| $[($out:extBinder)]*)
where
  onVars {α} (vars) (f : BinderName → M (Array α)) : M (Array α) := do
    if vars.size > 1 then
      warn! "warning: expanding binder group ({spaced repr vars})"
    vars.concatMapM (fun ⟨_, v⟩ => f v)
  trBasicBinder (vars ty) :=
    onVars vars fun v =>
      return #[← `(Std.ExtendedBinder.extBinder|
        $(trBinderIdent v):binderIdent $[: $(← ty.mapM fun ty => trExpr ty)]?)]

partial def trFunBinder : Binder → M (Array Syntax.FunBinder)
  | .«notation» .. => warn! "unsupported notation binder"
  | .binder bi vars bis ty _dflt => do
    let ty ← ty.mapM fun ty => trExprUnspanned (.Pi bis ty)
    let vars' := vars.getD #[Spanned.dummy .«_»] |>.map (trIdent_ ·.2)
    match bi, ty with
    | .implicit, _ => return #[← `(implicitBinderF| { $[$vars']* $[: $ty]? })]
    | .strictImplicit, _ => return #[← `(strictImplicitBinderF| ⦃ $[$vars']* $[: $ty]? ⦄)]
    | .instImplicit, _ =>
      let var ← vars.mapM fun
        | #[⟨_, .ident id⟩] => pure (mkIdent id)
        | _ => warn! "unsupported" | pure (mkIdent "_inst")
      return #[← `(Parser.Term.instBinder| [$[$var :]? $(ty.getD (← `(_)))])]
    | _default, none => pure (vars'.map (·))
    | _default, some ty =>
      if h : vars'.size > 0 then
        let app ← `($(vars'[0]) $(vars'[1:])*)
        return #[← `(($app : $ty))]
      else
        pure #[]
  | .collection bi vars n e =>
    let trBinder vars ty := trFunBinder <| .binder .default (some vars) #[] ty none
    expandBinderCollection trBinder bi vars n e

def trLambdaBinder : LambdaBinder → M (Array Syntax.FunBinder)
  | .reg bi => trFunBinder bi
  | .«⟨⟩» args => return #[← trExprUnspanned (.«⟨⟩» args)]

def trLetDecl : LetDecl → M (TSyntax ``Parser.Term.letDecl)
  | LetDecl.var x bis ty val => do
    let letId := mkNode ``Parser.Term.letIdDecl #[
      trIdent_ x.kind,
      mkNullNode $ ← trBinders {} bis,
      mkOptionalNode $ ← trOptType ty,
      mkAtom ":=", ← trExpr val]
    `(Parser.Term.letDecl| $letId:letIdDecl)
  | LetDecl.pat lhs val => do
    `(Parser.Term.letDecl| $(← trExpr lhs):term := $(← trExpr val))
  | LetDecl.notation _ => warn! "unsupported: let notation := ..."

def trDoElem : DoElem → M (TSyntax `doElem)
  | DoElem.let decl => do `(doElem| let $(← spanningS trLetDecl decl):letDecl)
  | DoElem.eval e => do `(doElem| $(← trExpr e):term)
  | DoElem.«←» lhs ty rhs els => do
    let rhs ← trExpr rhs
    match lhs.kind.unparen, els with
    | Expr.ident lhs, none =>
      `(doElem| let $(mkIdent lhs):ident $(← trOptType ty)? ← $rhs:term)
    | _, _ =>
      let els ← els.mapM trExpr
      `(doElem| let $(← trExpr lhs):term ← $rhs:term $[| $els:term]?)

def trProof : Proof → M Term
  | Proof.«from» _ e => trExpr e
  | Proof.block bl => do `(by $(← trBlock bl):tacticSeq)
  | Proof.by tac => do `(by $(← trTactic tac):tactic)

def trNotation (n : Choice) (args : Array (Spanned Arg)) : M Term := do
  let n ← match n with
  | Choice.one n => pure n
  | Choice.many ns =>
    if let some first := ns[0]? then
      if ns[1:].all (first == ·) then pure first else
        warn! "unsupported: ambiguous notation" | pure first
    else
      warn! "empty choice"
  match ← getNotationEntry? n, args with
  | some ⟨_, _, NotationKind.const stx, _⟩, #[] => pure stx
  | some ⟨_, _, NotationKind.const _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.unary f, _⟩, #[⟨m, Arg.expr e⟩] => f <$> trExpr ⟨m, e⟩
  | some ⟨_, _, NotationKind.unary _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binary f, _⟩, #[⟨m₁, Arg.expr e₁⟩, ⟨m₂, Arg.expr e₂⟩] =>
    return f (← trExpr ⟨m₁, e₁⟩) (← trExpr ⟨m₂, e₂⟩)
  | some ⟨_, _, NotationKind.binary _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.nary f, _⟩, args => f <$> args.mapM fun
    | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
    | ⟨m, Arg.binder bi⟩ => trExtBinders #[⟨m, bi⟩]
    | ⟨_, Arg.binders bis⟩ => trExtBinders bis
    | _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.exprs f, _⟩, #[⟨_, Arg.exprs es⟩] => f <$> es.mapM trExpr
  | some ⟨_, _, NotationKind.exprs _, _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[⟨mbi, Arg.binder bi⟩, ⟨me, Arg.expr e⟩] =>
    trExplicitBindersExt f g #[⟨mbi, bi⟩] ⟨me, e⟩
  | some ⟨_, _, NotationKind.binder f g, _⟩, #[⟨_, Arg.binders bis⟩, ⟨me, Arg.expr e⟩] =>
    trExplicitBindersExt f g bis ⟨me, e⟩
  | some ⟨_, _, NotationKind.binder .., _⟩, _ => warn! "unsupported (impossible)"
  | some ⟨_, _, NotationKind.fail, _⟩, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun
      | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
      | _ => warn! "unsupported notation {repr n}"
    `($(mkIdent n) $args*)
  | none, args =>
    warn! "warning: unsupported notation {repr n}"
    let args ← args.mapM fun
      | ⟨m, Arg.expr e⟩ => trExpr ⟨m, e⟩
      | _ => warn! "unsupported notation {repr n}"
    `($(mkIdent n) $args*)

def trBinary (n : Name) (lhs rhs : Term) : M Term := do
  match ← getNotationEntry? n with
  | some ⟨_, _, NotationKind.unary f, _⟩ => pure $ f lhs
  | some ⟨_, _, NotationKind.binary f, _⟩ => pure $ f lhs rhs
  | some ⟨_, _, NotationKind.nary f, _⟩ => pure $ f #[lhs, rhs]
  | _ =>
    warn! "warning: unsupported binary notation {repr n}"
    `($(mkIdent n) $lhs $rhs)

def trInfixFn (n : Choice) (e : Option (Spanned Expr)) : M Term := do
  let n ← match n with
  | Choice.one n => pure n
  | Choice.many ns =>
    if let some first := ns[0]? then
      if ns[1:].all (first == ·) then pure first else
        warn! "unsupported: ambiguous notation" | pure first
    else
      warn! "empty choice"
  let stx ← trBinary n mkCDot $ ← match e with
    | none => pure mkCDot
    | some e => trExpr e
  `(($stx))

def isSimpleBindersOnlyOptType? (bis : Array (Spanned Binder)) : Option (Array (Spanned BinderName) × Option (Spanned Expr)) := do
  if let #[⟨_, .binder .default (some bns) #[] ty none⟩] := bis then
    return (bns, ty)
  (·, none) <$> bis.concatMapM fun
    | ⟨_, .binder .default (some bns) #[] none none⟩ => bns
    | _ => none

partial def trLevel : Level → M Syntax.Level
  | Level.«_» => `(level| _)
  | Level.nat n => pure $ Quote.quote n
  | Level.add l n => do `(level| $(← trLevel l.kind) + $(Quote.quote n.kind))
  | Level.imax ls => do `(level| imax $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.max ls => do `(level| max $(← ls.mapM fun l => trLevel l.kind)*)
  | Level.param u => pure $ mkIdent u
  | Level.paren l => trLevel l.kind -- do `(level| ($(← trLevel l.kind)))

open Qq in
def trExpr' : Expr → M Term
  | Expr.«...» => `(_)
  | Expr.sorry => `(sorry)
  | Expr.«_» => `(_)
  | Expr.«()» => `(())
  | Expr.«{}» => `(Parser.Term.structInst| {})
  | Expr.ident n => mkIdentI n
  | Expr.const n none choices => mkIdentI n.kind choices
  | Expr.const n (some #[]) choices => mkIdentI n.kind choices
  | Expr.const n (some l) choices => do
    `($(← mkIdentI n.kind choices):ident.{$[$(← l.mapM fun e => trLevel e.kind):level],*})
  | Expr.nat n => pure $ Quote.quote n
  | Expr.decimal n d => pure (scientificLitOfDecimal n d).get!
  | Expr.string s => pure $ Syntax.mkStrLit s
  | Expr.char c => pure ⟨Syntax.mkCharLit c⟩
  | Expr.paren e => trExpr e -- do `(($(← trExpr e)))
  | Expr.sort ty st u => do
    match ty, if st then some Level._ else u.map Spanned.kind with
    | false, none => `(Sort)
    | false, some u => do `(Sort $(← trLevel u))
    | true, none => `(Type)
    | true, some u => do `(Type $(← trLevel u))
  | Expr.«→» lhs rhs => do `($(← trExpr lhs) → $(← trExpr rhs))
  | Expr.fun true #[⟨_, LambdaBinder.reg (Binder.binder _ none _ (some ty) _)⟩] e => do
    `(fun $(mkIdent `this):ident: $(← trExpr ty) => $(← trExpr e))
  | Expr.fun _ bis e => do
    if let #[⟨_, .reg (.binder .default (some bns) #[] ty none)⟩] := bis then
      let bns := bns.map fun ⟨m, bn⟩ => setInfoT m <| trIdent_ bn
      return ← `(fun $bns* $[: $(← ty.mapM trExpr)]? => $(← trExpr e))
    let bis ← bis.concatMapM (fun bi => trLambdaBinder bi.kind)
    `(fun $bis* => $(← trExpr e))
  | Expr.Pi #[] e => trExpr e
  | Expr.Pi bis e => do
    -- let dArrowHeuristic := !bis.any fun | ⟨_, Binder.binder _ _ _ none _⟩ => true | _ => false
    let dArrowHeuristic := false
    if dArrowHeuristic then trDArrow bis e else
      let bc := {}
      if let some (bns, ty) := isSimpleBindersOnlyOptType? bis then
        let bns := bns.map fun ⟨m, bn⟩ => setInfoT m <| trIdent_ bn
        return ← `(∀ $bns* $[: $(← ty.mapM trExpr)]?, $(← trExpr e))
      trExtendedBindersGrouped
        (fun | #[], e => e | args, e => Id.run `(∀ $args*, $e))
        (fun v pred e => Id.run `(∀ $v:binderIdent $pred:binderPred, $e))
        bc (← trBinders' bc bis) e
  | e@(Expr.app _ _) => do
    let (f, args) ← trAppArgs (Spanned.dummy e) trExpr
    `($f $args*)
  | Expr.show t pr => do
    `(show $(← trExpr t) from $(← trProof pr.kind))
  | Expr.have true h t pr e => do
    let h := h.map (mkIdent ·.kind)
    `(suffices $[$h:ident :]? $(← trExpr t) from $(← trProof pr.kind)
      $(← trExpr e))
  | Expr.have false h t pr e => do
    let t ← match t.kind with | Expr._ => pure none | _ => some <$> trExpr t
    let h := h.map (mkIdent ·.kind)
    `(have $[$h:ident]? $[: $t:term]? := $(← trProof pr.kind)
      $(← trExpr e))
  | Expr.«.» _ e pr => open Lean.TSyntax.Compat in do
    let pr ← match pr.kind with
    | Lean3.Proj.ident e => mkIdentF e
    | Lean3.Proj.nat n => pure $ Syntax.mkLit fieldIdxKind (toString n)
    pure $ mkNode ``Parser.Term.proj #[← trExpr e, mkAtom ".", pr]
  | Expr.if none c t e => do
    `(if $(← trExpr c) then $(← trExpr t) else $(← trExpr e))
  | Expr.if (some h) c t e => do
    `(if $(mkIdent h.kind):ident : $(← trExpr c)
      then $(← trExpr t) else $(← trExpr e))
  | Expr.calc args => do
    if h : args.size > 0 then
      `(calc $(← trCalcArg args[0]) $(← args[1:].toArray.mapM trCalcArg)*)
    else
      warn! "unsupported (impossible)"
  | Expr.«@» _ e => do `(@$(← trExpr e))
  | Expr.pattern e => trExpr e
  | Expr.«`()» _ true e => do `(q($(← trExpr e)))
  | Expr.«`()» false false e => do `(``($(← trExpr e)))
  | Expr.«`()» true false e => do `(`($(← trExpr e)))
  | Expr.«%%» e => do `($$($(← trExpr e)))
  | Expr.«`[]» _tacs => do
    warn! "warning: unsupported (TODO): `[tacs]"
    `(sorry)
  | Expr.«`» false n => pure $ Quote.quote n
  | Expr.«`» true n => do `(``$(← mkIdentI n):ident)
  | Expr.«⟨⟩» es => do `(⟨$(← es.mapM trExpr),*⟩)
  | Expr.infix_fn n e => trInfixFn n e
  | Expr.«(,)» es => do
    if h : es.size > 0 then
      `(($(← trExpr es[0]):term, $(← es[1:].toArray.mapM trExpr),*))
    else
      warn! "unsupported: empty (,)"
  | Expr.«.()» e => trExpr e
  | Expr.«:» e ty => do `(($(← trExpr e) : $(← trExpr ty)))
  | Expr.hole _es => warn! "unsupported: \{! ... !}"
  | Expr.«#[]» _es => warn! "unsupported: #[...]"
  | Expr.by tac => do `(by $(← trTactic tac):tactic)
  | Expr.begin tacs => do `(by $(← trBlock tacs):tacticSeq)
  | Expr.let bis e => do
    bis.foldrM (init := ← trExpr e) fun bi stx => do
      `(let $(← trLetDecl bi.kind):letDecl
        $stx)
  | Expr.match #[x] _ #[] => do `(nomatch $(← trExpr x))
  | Expr.match xs _ #[] => do `(match $[$(← xs.mapM trExpr):term],* with.)
  | Expr.match xs ty eqns => do
    `(match $[(motive := $(← ty.mapM trExpr))]? $[$(← xs.mapM trExpr):term],* with
      $[$(← eqns.mapM trArm):matchAlt]*)
  | Expr.do _ els => do let els ← els.mapM fun e => trDoElem e.kind; `(do $[$els:doElem]*)
  | Expr.«{,}» es => do `({$(← es.mapM trExpr):term,*})
  | Expr.subtype false x ty p => do
    `({$(mkIdent x.kind) $[: $(← ty.mapM trExpr)]? // $(← trExpr p)})
  | Expr.subtype true x none p => do `({$(mkIdent x.kind):ident | $(← trExpr p)})
  | Expr.subtype true x (some ty) p => do
    `({ $(mkIdent x.kind):ident : $(← trExpr ty):term | $(← trExpr p):term })
  | Expr.sep x ty p => do
    `({$(mkIdent x.kind):ident ∈ $(← trExpr ty) | $(← trExpr p)})
  | stx@(Expr.setReplacement _e _bis) => do
    warn!"unsupported set replacement {repr stx}"
    -- `({$(← trExpr e) | $[$(← trBinders {} bis):bracketedBinder]*})
  | Expr.structInst _ src flds srcs catchall => do
    let srcs := match src with | none => srcs | some src => #[src] ++ srcs
    let srcs := (← srcs.mapM (trExpr ·)).asNonempty
    let flds ← flds.mapM fun (lhs, rhs) => do
      let lhsId ← spanningS mkIdentF lhs
      withSpanS (lhs.meta.map fun m => {m with end_ := (rhs.meta.getD m).end_}) do
      if (match rhs with | ⟨_, Expr.ident rhs⟩ => rhs == lhs.kind | _ => false : Bool) then
        `(Parser.Term.structInstFieldAbbrev| $lhsId:ident)
      else
        `(Parser.Term.structInstField| $lhsId:ident := $(← trExpr rhs))
    if catchall then
      `({ $[$srcs,* with]? $[$flds]* .. })
    else
      `({ $[$srcs,* with]? $[$flds]* })
  | Expr.atPat lhs rhs => do `($(mkIdent lhs.kind)@ $(← trExpr rhs))
  | Expr.notation n args => trNotation n args
  | Expr.userNotation n args => do
    match (← get).userNotas.find? n with
    | some f => try f args catch e => warn! "in {n}: {← e.toMessageData.toString}"
    | none => warn! "unsupported user notation {n}"

