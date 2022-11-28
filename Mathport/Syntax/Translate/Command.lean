/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Syntax.Translate.Basic

namespace Mathport.Translate

open Lean hiding Expr Expr.app Expr.const Expr.sort Level Level.imax Level.max Level.param Command
open Lean.Elab (Visibility)
open Lean.Elab.Command (CommandElabM liftCoreM)
open Parser.Command AST3

def elabCommand (stx : Syntax.Command) : CommandElabM Unit := do
  -- try dbg_trace "warning: elaborating:\n{← liftCoreM $
  --   Lean.PrettyPrinter.parenthesizeCommand stx >>= Lean.PrettyPrinter.formatCommand}"
  -- catch e => dbg_trace "warning: failed to format: {← e.toMessageData.toString}\nin: {stx}"
  Elab.Command.elabCommand stx

def pushElab (stx : Syntax.Command) : M Unit := elabCommand stx *> push stx

def modifyScope (f : Scope → Scope) : M Unit :=
  modify fun s => { s with current := f s.current }

def pushScope : M Unit :=
  modify fun s => { s with scopes := s.scopes.push s.current }

def popScope : M Unit :=
  modify fun s => match s.scopes.back? with
  | none => s
  | some c => { s with current := c, scopes := s.scopes.pop }

def registerNotationEntry (loc : Bool) (d : NotationData) : M Unit :=
  if loc then modifyScope fun sc => { sc with localNotations := sc.localNotations.insert d }
  else registerGlobalNotationEntry d

def trDerive (e : Spanned AST3.Expr) : M Name :=
  match e.kind.unparen with
  | Expr.ident n => renameIdent n
  | Expr.const ⟨_, n⟩ _ choices => renameIdent n choices
  | e => warn! "unsupported derive handler {repr e}"

inductive TrAttr
  | del : TSyntax ``eraseAttr → TrAttr
  | add : Syntax.Attr → TrAttr
  | prio : Expr → TrAttr
  | parsingOnly : TrAttr
  | irreducible : TrAttr
  | derive : Array Name → TrAttr

def trAttr (_prio : Option Expr) : Attribute → M (Option TrAttr)
  | Attribute.priority n => pure $ TrAttr.prio n.kind
  | Attribute.del n => do
    let n ← match n with
    | `instance => pure `instance
    | `simp => pure `simp
    | `congr => pure `congr
    | `inline => pure `inline
    | `pattern => pure `match_pattern
    | _ => warn! "warning: unsupported attr -{n}"; return none
    pure $ some $ TrAttr.del (← `(eraseAttr| -$(← mkIdentI n)))
  | AST3.Attribute.add `parsing_only none => pure TrAttr.parsingOnly
  | AST3.Attribute.add `irreducible none => pure TrAttr.irreducible
  | AST3.Attribute.add n arg => do
    let attr ← match n, arg with
    | `class,              none => `(attr| class)
    | `instance,           none => `(attr| instance)
    | `simp,               none => `(attr| simp)
    | `recursor,           some ⟨_, AttrArg.indices #[]⟩ => warn! "unsupported: @[recursor]"
    | `recursor,           some ⟨_, AttrArg.indices #[⟨_, n⟩]⟩ =>
      `(attr| recursor $(Quote.quote n):num)
    | `intro,              none => `(attr| intro)
    | `intro,              some ⟨_, AttrArg.eager⟩ => `(attr| intro!)
    | `refl,               none => pure $ mkSimpleAttr `refl
    | `symm,               none => pure $ mkSimpleAttr `symm
    | `trans,              none => pure $ mkSimpleAttr `trans
    | `subst,              none => pure $ mkSimpleAttr `subst
    | `congr,              none => pure $ mkSimpleAttr `congr
    | `inline,             none => pure $ mkSimpleAttr `inline
    | `pattern,            none => pure $ mkSimpleAttr `match_pattern
    | `reducible,          none => pure $ mkSimpleAttr `reducible
    | `semireducible,      none => pure $ mkSimpleAttr `semireducible
    | `irreducible,        none => pure $ mkSimpleAttr `irreducible
    | `elab_simple,        none => pure $ mkSimpleAttr `elab_without_expected_type
    | `elab_as_eliminator, none => pure $ mkSimpleAttr `elab_as_elim
    | `vm_override,        some ⟨_, AttrArg.vmOverride n none⟩ =>
      pure $ mkSimpleAttr `implemented_by #[← mkIdentI n.kind]
    | `derive,             some ⟨_, AttrArg.user _ args⟩ =>
      return TrAttr.derive $ ← (← Parser.pExprListOrTExpr.run' args).mapM trDerive
    | `algebra,            _ => return none -- this attribute is no longer needed
    | _, none => mkSimpleAttr <$> renameAttr n
    | _, some ⟨_, AttrArg.user e args⟩ =>
      match (← get).userAttrs.find? n, args with
      | some f, _ =>
        let attr ← try f #[Spanned.dummy (AST3.Param.parse e args)]
        catch e => warn! "in {n}: {← e.toMessageData.toString}"
        if attr.raw.isMissing then return none
        pure attr
      | none, #[] => mkSimpleAttr <$> renameAttr n
      | none, _ => warn! "unsupported user attr {n}"
    | _, _ =>
      warn! "warning: suppressing unknown attr {n}"
      return none
    pure $ TrAttr.add attr

def trAttrKind : AttributeKind → M (TSyntax ``Parser.Term.attrKind)
  | .global => `(Parser.Term.attrKind|)
  | .scoped => `(Parser.Term.attrKind| scoped)
  | .local => `(Parser.Term.attrKind| local)

structure SpecialAttrs where
  prio : Option AST3.Expr := none
  parsingOnly := false
  irreducible := false
  derive : Array Name := #[]

def AttrState := SpecialAttrs × Array Syntax.EraseOrAttrInstance

def trAttrInstance (attr : Attribute) (allowDel := false)
  (kind : AttributeKind := .global) : StateT AttrState M Unit := do
  match ← trAttr (← get).1.prio attr with
  | some (TrAttr.del stx) => do
    unless allowDel do warn! "unsupported (impossible)"
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.add stx) => do
    let stx ← `(Parser.Term.attrInstance| $(← trAttrKind kind) $stx)
    modify fun s => { s with 2 := s.2.push stx }
  | some (TrAttr.prio prio) => modify fun s => { s with 1.prio := prio }
  | some TrAttr.parsingOnly => modify fun s => { s with 1.parsingOnly := true }
  | some TrAttr.irreducible => modify fun s => { s with 1.irreducible := true }
  | some (TrAttr.derive ns) => modify fun s => { s with 1.derive := s.1.derive ++ ns }
  | none => pure ()

def trAttributes (attrs : Attributes) (allowDel := false)
  (kind : AttributeKind := .global) : StateT AttrState M Unit :=
  attrs.forM fun attr => trAttrInstance attr.kind allowDel kind

structure Modifiers4 where
  docComment : Option String := none
  attrs : AttrState := ({}, #[])
  vis : Visibility := Visibility.regular
  «noncomputable» : Option Unit := none
  safety : DefinitionSafety := DefinitionSafety.safe

def trModifiers (mods : Modifiers) (more : Attributes := #[]) :
    M (SpecialAttrs × TSyntax ``declModifiers) :=
  mods.foldlM trModifier {} >>= trAttrs more >>= toSyntax
where
  trAttrs (attrs : Attributes) (kind : AttributeKind := .global)
    (s : Modifiers4) : M Modifiers4 := do
    pure { s with attrs := (← trAttributes attrs false kind s.attrs).2 }

  trModifier (s : Modifiers4) (m : Spanned Modifier) : M Modifiers4 :=
    match m.kind with
    | .private => match s.vis with
      | .regular => pure { s with vis := .private }
      | _ => throw! "unsupported (impossible)"
    | .protected => match s.vis with
      | .regular => pure { s with vis := .protected }
      | _ => throw! "unsupported (impossible)"
    | .noncomputable => match s.noncomputable with
      | none => pure { s with «noncomputable» := some () }
      | _ => throw! "unsupported (impossible)"
    | .meta => match s.safety with
      | .safe => pure { s with safety := .unsafe }
      | _ => throw! "unsupported (impossible)"
    | .mutual => pure s -- mutual is duplicated elsewhere in the grammar
    | .attr loc _ attrs => trAttrs attrs (if loc then .local else .global) s
    | .doc doc => match s.docComment with
      | none => pure { s with docComment := some doc }
      | _ => throw! "unsupported (impossible)"
  toSyntax : Modifiers4 → M (SpecialAttrs × TSyntax ``declModifiers)
  | ⟨doc, (s, attrs), vis, nc, safety⟩ => do
    let doc := doc.map trDocComment
    let attrs : Array (TSyntax ``Parser.Term.attrInstance) :=
      attrs.map fun s => ⟨s⟩ -- HACK HACK HACK ignores @[-attr]
    let attrs ← attrs.asNonempty.mapM fun attrs => `(Parser.Term.attributes| @[$[$attrs],*])
    let vis ← show M (Option (TSyntax [``«private», ``«protected»])) from match vis with
      | .regular => pure none
      | .private => `(«private»| private)
      | .protected => `(«protected»| protected)
    let nc ← nc.mapM fun () => `(«noncomputable»| noncomputable)
    let part ← match safety with
      | .partial => some <$> `(«partial»| partial)
      | _ => pure none
    let uns ← match safety with
      | .unsafe => some <$> `(«unsafe»| unsafe)
      | _ => pure none
    return (s, ← `(declModifiersF| $(doc)? $(attrs)? $(vis)? $(nc)? $(uns)? $(part)?))

def trOpenCmd (ops : Array Open) : M Unit := do
  let mut simple := #[]
  let pushSimple (s : Array Ident) :=
    unless s.isEmpty do pushElab $ ← `(command| open $[$s]*)
  for o in ops do
    match o with
    | ⟨tgt, none, clauses⟩ =>
      if clauses.isEmpty then
        simple := simple.push (← mkIdentN tgt.kind)
      else
        pushSimple simple; simple := #[]
        let mut explicit := #[]
        let mut renames := #[]
        let mut hides := #[]
        for c in clauses do
          match c.kind with
          | .explicit ns => explicit := explicit ++ ns
          | .renaming ns => renames := renames ++ ns
          | .hiding ns => hides := hides ++ ns
        match explicit.isEmpty, renames.isEmpty, hides.isEmpty with
        | true, true, true => pure ()
        | false, true, true =>
          let ns ← explicit.mapM fun n => mkIdentF n.kind
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident ($ns*))
        | true, false, true =>
          let rs ← renames.mapM fun ⟨a, b⟩ => do
            `(openRenamingItem| $(← mkIdentF a.kind):ident → $(← mkIdentF b.kind):ident)
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident renaming $rs,*)
        | true, true, false =>
          let ns ← hides.mapM fun n => mkIdentF n.kind
          pushElab $ ← `(command| open $(← mkIdentN tgt.kind):ident hiding $ns*)
        | _, _, _ => warn! "unsupported: advanced open style"
    | _ => warn! "unsupported: unusual advanced open style"
  pushSimple simple

def trExportCmd : Open → M Unit
  | ⟨tgt, none, clauses⟩ => do
    let mut args := #[]
    for c in clauses do
      match c.kind with
      | .explicit ns =>
        for n in ns do args := args.push (← mkIdentF n.kind)
      | _ => warn! "unsupported: advanced export style"
    pushElab $ ← `(export $(← mkIdentN tgt.kind):ident ($args*))
  | _ => warn! "unsupported: advanced export style"

def trDeclId (n : Name) (us : LevelDecl) : M (Option Name × TSyntax ``declId) := do
  let us := us.map $ Array.map fun u => mkIdent u.kind
  let orig := Elab.Command.resolveNamespace (← get).current.curNamespace n
  let ((dubious, n4), id) ← renameIdentCore n #[orig]
  if (← read).config.redundantAlign then
    pushAlign orig n4
  let (n3, _) := Rename.getClashes (← getEnv) n4
  let mut msg := Format.nil
  let mut found := none
  if dubious.isEmpty && (← getEnv).contains n4 && !binportTag.hasTag (← getEnv) n4 then
    found := n4 -- if the definition already exists, abort the current command
  if orig != n3 then
    if dubious.isEmpty then
      found := n4 -- if the clash is authoritative, abort the current command
    msg := msg ++ f!"warning: {orig} clashes with {n3} -> {n4}\n"
  if !dubious.isEmpty then
    msg := msg ++ f!"warning: {orig} -> {n4} is a dubious translation:\n{dubious}\n"
  if !msg.isEmpty then
    logComment f!"{msg}Case conversion may be inaccurate. Consider using '#align {orig} {n4}ₓ'."
  return (found, ← `(declId| $(← mkIdentR id):ident $[.{$us,*}]?))

def trDeclSig (bis : Binders) (ty : Option (Spanned Expr)) : M (TSyntax ``declSig) := do
  let bis ← trBinders {} bis
  let ty ← trExpr (ty.getD <| Spanned.dummy Expr.«_»)
  `(declSig| $[$bis]* : $ty)

def trOptDeclSig (bis : Binders) (ty : Option (Spanned Expr)) : M (TSyntax ``optDeclSig) := do
  let bis ← trBinders {} bis
  `(optDeclSig| $[$bis]* $[: $(← ty.mapM trExpr)]?)

def trAxiom (mods : Modifiers) (n : Name)
    (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr)) : M Unit := do
  let (s, mods) ← trModifiers mods
  unless s.derive.isEmpty do warn! "unsupported: @[derive] axiom"
  let (found, id) ← trDeclId n us
  withReplacement found do
    pushM `(command| $mods:declModifiers axiom $id $(← trDeclSig bis ty))

def trUWF : Option (Spanned Expr) →
    M (Option (TSyntax ``terminationByCore) × Option (TSyntax ``decreasingBy))
  | none | some ⟨_, AST3.Expr.«{}»⟩ => pure (none, none)
  | some ⟨_, AST3.Expr.structInst _ none flds #[] false⟩ => do
    let mut tm := none; let mut dc := none
    for (⟨_, n⟩, ⟨s, e⟩) in flds do
      match n with
      | `rel_tac =>
        let .fun _ _ ⟨_, .«`[]» #[⟨_, .interactive `exact #[⟨_, .parse _ #[⟨s, .expr e⟩]⟩]⟩]⟩ := e
          | warn! "warning: unsupported using_well_founded rel_tac: {repr e}"
        tm := some (← `(terminationByCore| termination_by' $(← trExpr ⟨s, e⟩):term))
      | `dec_tac =>
        dc := some (← `(decreasingBy| decreasing_by $(← trTactic (.dummy <| .expr ⟨s, e⟩)):tactic))
      | _ => warn! "warning: unsupported using_well_founded config option: {n}"
    if let some dc' := dc then
      -- this is a little optimistic, but let's hope that lean 4 doesn't need
      -- `decreasing_by assumption` as much as lean 3 did
      if dc' matches `(decreasingBy| decreasing_by assumption) then dc := none
    pure (tm, dc)
  | some _ => warn! "warning: unsupported using_well_founded config syntax" | pure (none, none)

def trDecl (dk : DeclKind) (mods : Modifiers) (attrs : Attributes)
    (n : Option (Spanned Name)) (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr))
    (val : DeclVal) (uwf : Option (Spanned Expr)) : M (Option Name × Syntax.Command) := do
  let (s, mods) ← trModifiers mods attrs
  let id ← n.mapM fun n => trDeclId n.kind us
  (id >>= (·.1), ·) <$> do
  let id := (·.2) <$> id
  let val ← match val with
    | DeclVal.expr e => `(declVal| := $(← trExprUnspanned e))
    | DeclVal.eqns #[] => `(declVal| := fun.)
    | DeclVal.eqns arms => `(declVal| $[$(← arms.mapM trArm):matchAlt]*)
  if s.irreducible then
    unless dk matches DeclKind.def do warn! "unsupported irreducible non-definition"
    unless s.derive.isEmpty do warn! "unsupported: @[derive, irreducible] def"
    unless uwf.isNone do warn! "unsupported: @[irreducible] def + using_well_founded"
    return ← `($mods:declModifiers irreducible_def $id.get! $(← trOptDeclSig bis ty) $val:declVal)
  match dk with
  | DeclKind.abbrev => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] abbrev"
    unless uwf.isNone do warn! "unsupported: abbrev + using_well_founded"
    `($mods:declModifiers abbrev $id.get! $(← trOptDeclSig bis ty):optDeclSig $val)
  | DeclKind.def => do
    let ds := s.derive.map mkIdent |>.asNonempty
    let (tm, dc) ← trUWF uwf
    `($mods:declModifiers
      def $id.get! $(← trOptDeclSig bis ty) $val:declVal $[deriving $ds,*]? $(tm)? $(dc)?)
  | DeclKind.example => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] example"
    unless uwf.isNone do warn! "unsupported: example + using_well_founded"
    `($mods:declModifiers example $(← trOptDeclSig bis ty):optDeclSig $val)
  | DeclKind.theorem => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] theorem"
    let (tm, dc) ← trUWF uwf
    `($mods:declModifiers
      theorem $id.get! $(← trDeclSig bis ty) $val:declVal $(tm)? $(dc)?)
  | DeclKind.instance => do
    unless s.derive.isEmpty do warn! "unsupported: @[derive] instance"
    let prio ← s.prio.mapM fun prio => do
      `(namedPrio| (priority := $(← trPrio prio)))
    let sig ← trDeclSig bis ty
    let (tm, dc) ← trUWF uwf
    `($mods:declModifiers
      instance $[$prio:namedPrio]? $[$id:declId]? $sig $val:declVal $(tm)? $(dc)?)

def trOptDeriving : Array Name → M (TSyntax ``optDeriving)
  | #[] => `(optDeriving|)
  | ds => `(optDeriving| deriving $[$(ds.map mkIdent):ident],*)

set_option linter.unusedVariables false in -- FIXME(Mario): spurious warning on let ctors ← ...
def trInductive (cl : Bool) (mods : Modifiers) (attrs : Attributes)
  (n : Spanned Name) (us : LevelDecl) (bis : Binders) (ty : Option (Spanned Expr))
  (nota : Option Notation) (intros : Array (Spanned Intro)) : M (Option Name × Syntax.Command) := do
  let (s, mods) ← trModifiers mods attrs
  let (found, id) ← trDeclId n.kind us
  (found, ·) <$> do
  let sig ← trOptDeclSig bis ty
  unless nota.isNone do warn! "unsupported: (notation) in inductive"
  let ctors ← intros.mapM fun ⟨m, ⟨doc, name, ik, bis, ty⟩⟩ => withSpanS m do
    if let some ik := ik then warn! "infer kinds are unsupported in Lean 4: {name.2} {ik}"
    `(ctor| $[$(doc.map trDocComment):docComment]?
      | $(← mkIdentI name.kind):ident $(← trOptDeclSig bis ty):optDeclSig)
  let ds ← trOptDeriving s.derive
  match cl with
  | true => `($mods:declModifiers class inductive
    $id:declId $sig:optDeclSig $[$ctors:ctor]* $ds:optDeriving)
  | false => `($mods:declModifiers inductive
    $id:declId $sig:optDeclSig $[$ctors:ctor]* $ds:optDeriving)

def trMutual (decls : Array (Mutual α)) (uwf : Option (Spanned Expr))
    (f : Mutual α → M (Option Name × Syntax.Command)) : M Unit := do
  let mut found := none
  let mut cmds := #[]
  for decl in decls do
    let (found', cmd) ← f decl
    found := found <|> found'
    cmds := cmds.push cmd
  let (tm, dc) ← trUWF uwf
  withReplacement found do pushM `(mutual $cmds* end $(tm)? $(dc)?)

def trField : Spanned Field → M (Array Syntax) := spanning fun
  | Field.binder bi ns ik bis ty dflt => do
    let ns ← ns.mapM fun n => mkIdentF n.kind
    if let some ik := ik then warn! "infer kinds are unsupported in Lean 4: {ns} {ik}"
    (#[·]) <$> match bi with
    | BinderInfo.implicit => do
      `(structImplicitBinder| {$ns* $(← trDeclSig bis ty):declSig})
    | BinderInfo.instImplicit => do
      `(structInstBinder| [$ns* $(← trDeclSig bis ty):declSig])
    | _ => do
      let sig ← trOptDeclSig bis ty
      let dflt ← dflt.mapM trBinderDefault
      if let #[n] := ns then
        `(structSimpleBinder| $n:ident $sig:optDeclSig $[$dflt]?)
      else
        `(structExplicitBinder| ($ns* $sig:optDeclSig $[$dflt]?))
  | Field.notation _ => warn! "unsupported: (notation) in structure"

def trFields (flds : Array (Spanned Field)) : M (TSyntax ``structFields) := do
  let flds ← flds.concatMapM trField
  pure $ mkNode ``structFields #[mkNullNode flds]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let (s, mods) ← trModifiers mods
  let (found, id) ← trDeclId n.kind us
  withReplacement found do
  let bis ← trBracketedBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, false, none, ty, #[]⟩ => trExpr ty
    | _ => warn! "unsupported: advanced extends in structure"
  let exts ← exts.asNonempty.mapM fun exts => `(«extends»| extends $[$exts],*)
  let ty ← trOptType ty
  let (ctor, flds) ← match mk, flds with
    | none, #[] => pure (none, none)
    | mk, flds => do
      let mk ← mk.mapM fun ⟨_, n, ik⟩ => do
        if let some ik := ik then warn! "infer kinds are unsupported in Lean 4: {n.2} {ik}"
        `(structCtor| $(← mkIdentF n.kind):ident ::)
      pure (some mk, some (← trFields flds))
  let deriv ← trOptDeriving s.derive
  let decl ←
    if cl then
      `(«structure»|
        class $id:declId $[$bis]* $[$exts]? $[$ty]? $[where $[$ctor]? $flds]? $deriv)
    else
      `(«structure»|
        structure $id:declId $[$bis]* $[$exts]? $[$ty]? $[where $[$ctor]? $flds]? $deriv)
  pushM `(command| $mods:declModifiers $decl:structure)

partial def mkUnusedName [Monad m] [MonadResolveName m] [MonadEnv m]
  (baseName : Name) : m Name := do
  let ns ← getCurrNamespace
  let env ← getEnv
  return if env.contains (ns ++ baseName) then
    let rec loop (idx : Nat) :=
      let name := baseName.appendIndexAfter idx
      if env.contains (ns ++ name) then loop (idx+1) else name
    loop 1
  else baseName

section

private def mkNAry (lits : Array (Spanned AST3.Literal)) : Option (Array Literal) := do
  let mut i := 0
  let mut out := #[]
  for lit in lits do
    match lit with
    | ⟨_, AST3.Literal.sym tk⟩ => out := out.push (Literal.tk tk.1.kind.toString)
    | ⟨_, AST3.Literal.var _ _⟩ => out := out.push (Literal.arg i); i := i + 1
    | ⟨_, AST3.Literal.binder _⟩ => out := out.push (Literal.arg i); i := i + 1
    | ⟨_, AST3.Literal.binders _⟩ => out := out.push (Literal.arg i); i := i + 1
    | _ => none
  pure out

partial def trPrecExpr : Expr → M Precedence
  | Expr.nat n => pure $ Precedence.nat n
  | Expr.paren e => trPrecExpr e.kind -- do `(prec| ($(← trPrecExpr e.kind)))
  | Expr.const ⟨_, `max⟩ _ _ => pure Precedence.max
  | Expr.const ⟨_, `std.prec.max_plus⟩ _ _ => pure Precedence.maxPlus
  | Expr.notation (Choice.one `«expr + ») #[
      ⟨_, Arg.expr (Expr.ident `max)⟩,
      ⟨_, Arg.expr (Expr.nat 1)⟩
    ] => pure Precedence.maxPlus
  | e => warn! "unsupported: advanced prec syntax {repr e}" | pure $ Precedence.nat 999

def trPrec : AST3.Precedence → M Precedence
  | AST3.Precedence.nat n => pure $ Precedence.nat n
  | AST3.Precedence.expr e => trPrecExpr e.kind

private def isIdentPrec : AST3.Literal → Bool
  | AST3.Literal.sym _ => true
  | AST3.Literal.var _ none => true
  | AST3.Literal.var _ (some ⟨_, Action.prec _⟩) => true
  | _ => false

private def truncatePrec (prec : Precedence) : Precedence := Id.run do
  -- https://github.com/leanprover-community/mathport/issues/114#issuecomment-1046582957
  if let Precedence.nat n := prec then
    if n > 1024 then
      return Precedence.nat 1024
  return prec

private def trMixfix (kind : TSyntax ``Parser.Term.attrKind) (prio : Option (TSyntax ``namedPrio))
    (m : AST3.MixfixKind) (tk : String) (prec : Option (Spanned AST3.Precedence)) :
    M (NotationDesc × (Option (TSyntax ``namedName) → Term → Id Syntax.Command)) := do
  let p ← match prec with
  | some p => trPrec p.kind
  | none => pure $ (← getPrecedence? tk m).getD (Precedence.nat 0)
  let p := truncatePrec p
  let p := p.toSyntax
  let s := Syntax.mkStrLit tk
  pure $ match m with
  | MixfixKind.infix | MixfixKind.infixl =>
    (NotationDesc.infix tk, fun n e =>
      `($kind:attrKind infixl:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.infixr =>
    (NotationDesc.infix tk, fun n e =>
      `($kind:attrKind infixr:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.prefix =>
    (NotationDesc.prefix tk, fun n e =>
      `($kind:attrKind prefix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))
  | MixfixKind.postfix =>
    (NotationDesc.postfix tk, fun n e =>
      `($kind:attrKind postfix:$p $[$n:namedName]? $[$prio:namedPrio]? $s => $e))

private def trNotation4 (kind : TSyntax ``Parser.Term.attrKind)
    (prio : Option (TSyntax ``namedPrio)) (p : Option Prec) (lits : Array (Spanned AST3.Literal)) :
    M (Option (TSyntax ``namedName) → Term → Id Syntax.Command) := do
  let lits ← lits.mapM fun
  | ⟨_, AST3.Literal.sym tk⟩ => `(notationItem| $(Syntax.mkStrLit tk.1.kind.toString):str)
  | ⟨_, AST3.Literal.var x none⟩ => `(notationItem| $(mkIdent x.kind):ident)
  | ⟨_, AST3.Literal.var x (some ⟨_, Action.prec p⟩)⟩ => do
    `(notationItem| $(mkIdent x.kind):ident : $((← trPrec p).toSyntax))
  | _ => warn! "unsupported (impossible)"
  pure fun n e =>
    `($kind:attrKind notation$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

open Lean.Parser.Command in
private def trNotation3Item : (lit : AST3.Literal) → M (Array (TSyntax ``notation3Item))
  | .sym tk => pure #[sym tk]
  | .binder .. | .binders .. => return #[← `(notation3Item| (...))]
  | .var x none
  | .var x (some ⟨_, .prec _⟩)
  | .var x (some ⟨_, .prev⟩) => pure #[var x]
  | .var x (some ⟨_, .scoped _ sc⟩) => return #[← scope x sc]
  | .var x (some ⟨_, .fold r _ sep «rec» (some ini) term⟩) => do
    let f ← fold x r sep «rec» ini
    pure $ match term.map sym with | none => #[f] | some a => #[f, a]
  | lit => warn! "unsupported: advanced notation ({repr lit})"
where
  sym tk := Id.run `(notation3Item| $(Syntax.mkStrLit tk.1.kind.toString):str)
  var x := Id.run `(notation3Item| $(mkIdent x.kind):ident)
  scope x sc := do
    let (p, e) := match sc with
      | none => (`x, Spanned.dummy $ Expr.ident `x)
      | some (p, e) => (p.kind, e)
    `(notation3Item| $(mkIdent x.kind):ident : (scoped $(mkIdent p) => $(← trExpr e)))
  fold x r sep | (y, z, «rec»), ini => do
    let kind ← if r then `(foldKind| foldr) else `(foldKind| foldl)
    `(notation3Item| ($(mkIdent x.kind) $(Syntax.mkStrLit sep.1.kind.toString)* =>
        $kind ($(mkIdent y.kind) $(mkIdent z.kind) => $(← trExpr rec)) $(← trExpr ini)))

private def addSpaceBeforeBinders (lits : Array AST3.Literal) : Array AST3.Literal := Id.run do
  let mut lits := lits
  for i in [1:lits.size] do
    if lits[i]! matches AST3.Literal.binder .. || lits[i]! matches AST3.Literal.binders .. then
      if let AST3.Literal.sym (⟨s, Symbol.quoted tk⟩, prec) := lits[i-1]! then
        if !tk.endsWith " " then
          lits := lits.set! (i-1) <| AST3.Literal.sym (⟨s, Symbol.quoted (tk ++ " ")⟩, prec)
  lits

private def trNotation3 (kind : TSyntax ``Parser.Term.attrKind)
    (prio : Option (TSyntax ``namedPrio)) (p : Option Prec) (lits : Array (Spanned AST3.Literal)) :
    M (Option (TSyntax ``namedName) → Term → Id Syntax.Command) := do
  let lits := addSpaceBeforeBinders <| lits.map (·.kind)
  let lits ← lits.concatMapM trNotation3Item
  pure fun n e =>
    `($kind:attrKind notation3$[:$p]? $[$n:namedName]? $[$prio:namedPrio]? $lits* => $e)

def trNotationCmd (kind : AttributeKind) (res : Bool) (attrs : Attributes) (nota : Notation)
  (ns : Option Name := none) : M Unit := do
  let (s, attrs) := (← trAttributes attrs false .global |>.run ({}, #[])).2
  unless s.derive.isEmpty do warn! "unsupported: @[derive] notation"
  unless attrs.isEmpty do warn! "unsupported (impossible)"
  if res then
    match nota with
    | Notation.mixfix m _ (tk, some prec) _ =>
      registerPrecedenceEntry tk.kind.toString m (← trPrec prec.kind)
    | _ => warn! "warning: suppressing unsupported reserve notation"
    return
  let n := nota.name3
  let skip : Bool := match ← getNotationEntry? n with
  | some ⟨_, _, _, skip⟩ => skip
  | none => false
  if skip && kind != .local then return
  let prio ← s.prio.mapM fun prio => do `(namedPrio| (priority := $(← trPrio prio)))
  let kindStx ← trAttrKind kind
  let (e, desc, cmd) ← match nota with
  | Notation.mixfix m _ (tk, prec) (some e) =>
    pure (e, ← trMixfix kindStx prio m tk.kind.toString prec)
  | Notation.notation _ lits (some e) =>
    let p := match lits.get? 0 with
    | some ⟨_, AST3.Literal.sym tk⟩ => tk.2
    | some ⟨_, AST3.Literal.var _ _⟩ => match lits.get? 1 with
      | some ⟨_, AST3.Literal.sym tk⟩ => tk.2
      | _ => none
    | _ => none
    let p ← p.mapM fun p => return (← trPrec p.kind).toSyntax
    let desc := match lits with
    | #[⟨_, AST3.Literal.sym tk⟩] => NotationDesc.const tk.1.kind.trim
    | #[⟨_, AST3.Literal.sym left⟩,
        ⟨_, AST3.Literal.var _ (some ⟨_, Action.fold _ _ sep _ _ (some term)⟩)⟩] =>
      NotationDesc.exprs left.1.kind.trim sep.1.kind.trim term.1.kind.trim
    | _ => match mkNAry lits with
      | some lits => NotationDesc.nary lits
      | none => NotationDesc.fail
    let cmd ← match lits.all fun lit => isIdentPrec lit.kind with
    | true => trNotation4 kindStx prio p lits
    | false => trNotation3 kindStx prio p lits
    pure (e, desc, cmd)
  | _ => warn! "unsupported (impossible)" | default
  let e ← trExpr e
  let ns' := match ns with
  | none => .anonymous
  | some ns => rootNamespace ++ ns
  let n4 ← Elab.Command.withWeakNamespace (ns' ++ (← getEnv).mainModule) $ do
    let n4 ← mkUnusedName nota.name4
    let nn ← `(namedName| (name := $(mkIdent n4)))
    try elabCommand (cmd (some nn) e)
    catch e => dbg_trace "warning: failed to add syntax {repr n4}: {← e.toMessageData.toString}"
    pure $ (← getCurrNamespace) ++ n4
  printOutput s!"-- mathport name: {n}\n"
  if let some ns := ns then
    pushM `(command| scoped[$(← mkIdentR ns)] $(cmd none e))
  else push (cmd none e)
  registerNotationEntry (kind == .local) ⟨n, n4, desc⟩

end

def trInductiveCmd : InductiveCmd → M Unit
  | InductiveCmd.reg cl mods n us bis ty nota intros => do
    let (found, cmd) ← trInductive cl mods #[] n us bis ty nota intros
    withReplacement found (push cmd)
  | InductiveCmd.mutual cl mods us bis nota inds =>
    trMutual inds none fun ⟨attrs, n, ty, intros⟩ => do
      trInductive cl mods attrs n us bis ty nota intros

def trAttributeCmd (kind : AttributeKind) (attrs : Attributes) (ns : Array (Spanned Name))
    (f : Syntax.Command → Syntax.Command) : M Unit := do
  if ns.isEmpty then return ()
  let (s, attrs) := (← trAttributes attrs true kind |>.run ({}, #[])).2
  let ns ← ns.mapM fun n => mkIdentI n.kind
  unless s.derive.isEmpty do
    push $ f $ ← `(deriving instance $[$(s.derive.map mkIdent):ident],* for $ns,*)
  unless attrs.isEmpty do
    push $ f $ ← `(attribute [$attrs,*] $ns*)

def trCommand' : Command → M Unit
  | Command.initQuotient => pushM `(init_quot)
  | Command.mdoc doc =>
    push ⟨mkNode ``moduleDoc #[mkAtom "/-!", mkAtom (doc ++ "-/")]⟩
  | Command.«universe» _ _ ns =>
    pushM `(universe $(ns.map fun n => mkIdent n.kind)*)
  | Command.«namespace» n => do
    pushScope; modifyScope fun s => { s with curNamespace := s.curNamespace ++ n.kind }
    pushElab $ ← `(namespace $(← mkIdentN n.kind))
  | Command.«section» n => do
    pushScope; pushElab $ ← `(section $(← n.mapM fun n => mkIdentN n.kind)?)
  | Command.«end» n => do
    popScope; pushElab $ ← `(end $(← n.mapM fun n => mkIdentN n.kind)?)
  | Command.«variable» vk _ _ bis =>
    unless bis.isEmpty do
      let bis ← trBracketedBinders {} bis
      match vk with
      | VariableKind.variable => pushM `(variable $bis*)
      | VariableKind.parameter => pushM `(parameter $bis*)
  | Command.axiom _ mods n us bis ty => trAxiom mods n.kind us bis ty
  | Command.axioms _ mods bis => bis.forM fun
    | ⟨_, Binder.binder _ (some ns) bis (some ty) none⟩ => ns.forM fun
      | ⟨_, BinderName.ident n⟩ => trAxiom mods n none bis ty
      | _ => warn! "unsupported (impossible)"
    | _ => warn! "unsupported (impossible)"
  | Command.decl dk mods n us bis ty val uwf => do
    let (found, cmd) ← trDecl dk mods #[] n us bis ty val.kind uwf
    withReplacement found (push cmd)
  | Command.mutualDecl dk mods us bis arms uwf =>
    trMutual arms uwf fun ⟨attrs, n, ty, vals⟩ =>
      trDecl dk mods attrs n us bis ty (DeclVal.eqns vals) none
  | Command.inductive ind => trInductiveCmd ind
  | Command.structure cl mods n us bis exts ty m flds =>
    trStructure cl mods n us bis exts ty m flds
  | Command.attribute loc _ attrs ns =>
    trAttributeCmd (if loc then .local else .global) attrs ns id
  | Command.precedence .. => warn! "warning: unsupported: precedence command"
  | Command.notation (loc, res) attrs n =>
    trNotationCmd (if loc then .local else .global) res attrs n
  | Command.open true ops => ops.forM trExportCmd
  | Command.open false ops => trOpenCmd ops
  | Command.include true ops => unless ops.isEmpty do
      pushM `(include $(ops.map fun n => mkIdent n.kind)*)
  | Command.include false ops => unless ops.isEmpty do
      pushM `(omit $(ops.map fun n => mkIdent n.kind)*)
  | Command.hide ops => unless ops.isEmpty do
      warn! "unsupported: hide command"
      -- pushM `(hide $(ops.map fun n => mkIdent n.kind)*)
  | Command.theory #[⟨_, Modifier.noncomputable⟩] =>
    pushM `(command| noncomputable section)
  | Command.theory #[⟨_, Modifier.doc doc⟩, ⟨_, Modifier.noncomputable⟩] => do
    printOutput s!"/-!{doc}-/\n"
    pushM `(command| noncomputable section)
  | Command.theory _ => warn! "unsupported (impossible)"
  | Command.setOption o val => match o.kind, val.kind with
    | `old_structure_cmd, OptionVal.bool b =>
      modifyScope fun s => { s with oldStructureCmd := b }
    | o, OptionVal.bool true => do
      pushM `(command| set_option $(← mkIdentO o) true)
    | o, OptionVal.bool false => do
      pushM `(command| set_option $(← mkIdentO o) false)
    | o, OptionVal.str s => do
      pushM `(command| set_option $(← mkIdentO o) $(Syntax.mkStrLit s):str)
    | o, OptionVal.nat n => do
      pushM `(command| set_option $(← mkIdentO o) $(Quote.quote n):num)
    | _, OptionVal.decimal .. => warn! "unsupported: float-valued option"
  | Command.declareTrace n => do
    let n ← renameIdent n.kind
    pushM `(command| initialize registerTraceClass $(Quote.quote n))
  | Command.addKeyEquivalence .. => warn! "unsupported: add_key_equivalence"
  | Command.runCmd e => do let e ← trExpr e; pushM `(run_cmd $e:term)
  | Command.check e => do pushM `(#check $(← trExpr e))
  | Command.reduce _ e => do pushM `(#reduce $(← trExpr e))
  | Command.eval e => do pushM `(#eval $(← trExpr e))
  | Command.unify .. => warn! "unsupported: #unify"
  | Command.compile .. => warn! "unsupported: #compile"
  | Command.help .. => warn! "unsupported: #help"
  | Command.print (PrintCmd.str s) => pushM `(#print $(Syntax.mkStrLit s))
  | Command.print (PrintCmd.ident n) => do pushM `(#print $(← mkIdentI n.kind))
  | Command.print (PrintCmd.axioms (some n)) => do pushM `(#print axioms $(← mkIdentI n.kind))
  | Command.print _ => warn! "unsupported: advanced #print"
  | Command.userCommand n mods args => do
    match (← get).userCmds.find? n with
    | some f => try f mods args catch e => warn! "in {n} {repr args}: {← e.toMessageData.toString}"
    | none => warn! "unsupported user command {n}"
