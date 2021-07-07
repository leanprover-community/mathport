/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.AST3
import Mathport.Data4
import Mathport.Parse

namespace Mathport

open Lean hiding Expr
open Lean.Elab (Visibility)

namespace Translate

open Std (HashMap)
open AST3

syntax (name := cmdQuot) "`(command|" incQuotDepth(command) ")" : term

open Lean Elab Term Quotation in
@[termElab cmdQuot] def elabCmdQuot : TermElab := adaptExpander stxQuot.expand

structure Context where

structure Scope where
  oldStructureCmd : Bool
  deriving Inhabited

structure State where
  «prelude» : Bool
  imports : Array Name
  commands : Array Syntax
  current : Scope
  scopes : Array Scope
  deriving Inhabited

abbrev M := ReaderT Context (StateRefT State CoreM)

local instance : MonadQuotation CoreM where
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
  modify fun s => { s with current := s.scopes.back, scopes := s.scopes.pop }

def WithArray (α β : Type) : Nat → Type
  | 0 => M β
  | n+1 => α → WithArray α β n

instance [Inhabited β] : Inhabited (WithArray α β n) := ⟨go n⟩ where go
  | 0 => (inferInstanceAs (Inhabited (M β))).default
  | n+1 => fun _ => go n

@[inline] def withArray [Inhabited β] (a : Array α) := go 0 where
  go : Nat → (n : Nat) → WithArray α β n → M β
  | i, 0, f => if i = a.size then f else throwError "array size mismatch"
  | i, n+1, f =>
    if h : _ then go (i+1) n (f $ a.get ⟨i, h⟩)
    else throwError "array size mismatch"

def trDocComment (doc : String) : Syntax :=
  mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ "-/")]

structure BinderContext where
  -- if true, only allow simple for no type
  allowSimple : Option Bool := none
  requireType := false

def trTacticSeq : Tactic → M Syntax
  | _ => throwError "unsupported (TODO)"

def trExpr : Expr → M Syntax
  | _ => throwError "unsupported (TODO)"

def trPrio : Expr → M Syntax
  | _ => throwError "unsupported (TODO)"

def trBinderName : BinderName → Syntax
  | BinderName.ident n => mkIdent n
  | BinderName.«_» => mkHole arbitrary

def trBinderDefault (allowTac := true) : Default → M Syntax
  | Default.«:=» e => do `(Parser.Term.binderDefault| := $(← trExpr e.kind))
  | Default.«.» e => do
    unless allowTac do throwError "unsupported"
    `(Parser.Term.binderTactic| := by $(← trTacticSeq $ Tactic.expr $ e.map Expr.ident))

def trBinder : BinderContext → Binder → Array Syntax → M (Array Syntax)
  | _, Binder.binder BinderInfo.instImplicit vars _ (some ty) none, out => do
    let var ← match vars with
    | none => #[]
    | some vars => withArray vars 1 fun v => pure #[trBinderName v.kind, mkAtom ":"]
    out.push $ mkNode ``Parser.Term.instBinder
      #[mkAtom "[", mkNode nullKind var, ← trExpr ty.kind, mkAtom "]"]
  | ⟨some true, _⟩, Binder.binder BinderInfo.default (some vars) #[] none none, out =>
    out.push <$> trSimple vars none
  | ⟨some false, _⟩, Binder.binder BinderInfo.default (some vars) #[] ty none, out =>
    out.push <$> trSimple vars ty
  | ⟨_, req⟩, Binder.binder bi (some vars) bis ty dflt, out => do
    let vars := mkNode nullKind $ vars.map fun v => trBinderName v.kind
    let ty := match req, ty with
    | true, none => some Expr.«_»
    | _, _ => ty.map fun ty => ty.kind
    let ty ← mkNode nullKind <$> match ty with
    | none => #[]
    | some ty => do pure #[mkAtom ":", ← trExpr ty]
    if bi == BinderInfo.implicit then
      out.push $ mkNode ``Parser.Term.implicitBinder #[mkAtom "(", vars, ty, mkAtom ")"]
    else
      let dflt ← mkOptionalNode <$> dflt.mapM trBinderDefault
      out.push $ mkNode ``Parser.Term.explicitBinder #[mkAtom "(", vars, ty, dflt, mkAtom ")"]
  | _, _, _ => throwError "unsupported"
where
  trSimple vars ty : M Syntax := do
    let vars := mkNode nullKind $ vars.map fun v => trBinderName v.kind
    let ty ← ty.mapM fun ty => trExpr ty.kind
    mkNode ``Parser.Term.simpleBinder #[vars, mkOptionalNode ty]

def trBinders (bc : BinderContext) (bis : Array (Spanned Binder)) : M (Array Syntax) := do
  bis.foldlM (fun out bi => trBinder bc bi.kind out) #[]

inductive TrAttr
  | del : Syntax → TrAttr
  | add : Syntax → TrAttr
  | prio : Expr → TrAttr

def trAttr (prio : Option Expr) : Attribute → M TrAttr
  | Attribute.priority n => TrAttr.prio n.kind
  | Attribute.del n => do TrAttr.del (← `(Parser.Command.eraseAttr| -$(mkIdent n)))
  | AST3.Attribute.add n arg => throwError "unsupported (TODO)"

def trAttrKind : AttributeKind → M Syntax
  | AttributeKind.global => `(Parser.Term.attrKind|)
  | AttributeKind.scoped => `(Parser.Term.attrKind| scoped)
  | AttributeKind.local => `(Parser.Term.attrKind| local)

structure AttrState where
  prio : Option AST3.Expr := none
  out : Array Syntax := #[]

def trAttrInstance (attr : Attribute) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit := do
  match ← trAttr (← get).1 attr with
  | TrAttr.del stx => do
    unless allowDel do throwError "unsupported"
    modify fun s => { s with out := s.out.push stx }
  | TrAttr.add stx => do
    let stx := mkNode ``Parser.Term.attrInstance #[← trAttrKind kind, stx]
    modify fun s => { s with out := s.out.push stx }
  | TrAttr.prio prio => modify fun s => { s with prio := prio }

def trAttributes (attrs : Attributes) (allowDel := false)
  (kind : AttributeKind := AttributeKind.global) : StateT AttrState M Unit :=
  attrs.forM fun attr => trAttrInstance attr.kind allowDel kind

structure Modifiers4 where
  docComment : Option String := none
  attrs : AttrState := {}
  vis : Visibility := Visibility.regular
  «noncomputable» : Option Unit := none
  safety : DefinitionSafety := DefinitionSafety.safe

def mkOpt (a : Option α) (f : α → M Syntax) : M Syntax :=
  match a with
  | none => mkNode nullKind #[]
  | some a => do mkNode nullKind #[← f a]

def trModifiers (mods : Modifiers) : M (Option Expr × Syntax) :=
  mods.foldlM trModifier {} >>= toSyntax
where
  trModifier (s : Modifiers4) (m : Spanned Modifier) : M Modifiers4 :=
    match m.kind with
    | Modifier.private => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.private }
      | _ => throwError "unsupported"
    | Modifier.protected => match s.vis with
      | Visibility.regular => pure { s with vis := Visibility.protected }
      | _ => throwError "unsupported"
    | Modifier.noncomputable => match s.noncomputable with
      | none => pure { s with «noncomputable» := some () }
      | _ => throwError "unsupported"
    | Modifier.meta => match s.safety with
      | DefinitionSafety.safe => pure { s with safety := DefinitionSafety.unsafe }
      | _ => throwError "unsupported"
    | Modifier.mutual => s -- mutual is duplicated elsewhere in the grammar
    | Modifier.attr loc _ attrs => do
      let kind := if loc then AttributeKind.local else AttributeKind.global
      pure { s with attrs := (← trAttributes attrs false kind |>.run {}).2 }
    | Modifier.doc doc => match s.docComment with
      | none => pure { s with docComment := some doc }
      | _ => throwError "unsupported"
  toSyntax : Modifiers4 → M (Option Expr × Syntax)
  | ⟨doc, ⟨prio, attrs⟩, vis, nc, safety⟩ => do
    let doc := mkOptionalNode $ doc.map trDocComment
    let attrs ← mkOpt (if attrs.isEmpty then none else some attrs) fun attrs =>
      `(Parser.Term.attributes| @[$[$attrs],*])
    let vis := mkOptionalNode $ match vis with
    | Visibility.regular => none
    | Visibility.private => mkAtom "private"
    | Visibility.protected => mkAtom "protected"
    let nc ← mkOpt nc fun () => mkAtom "noncomputable"
    let part := mkOptionalNode $ match safety with
    | DefinitionSafety.partial => mkAtom "partial"
    | _ => none
    let uns := mkOptionalNode $ match safety with
    | DefinitionSafety.unsafe => mkAtom "unsafe"
    | _ => none
    (prio, mkNode ``Parser.Command.declModifiers #[doc, attrs, vis, nc, part, uns])

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
        | _, _, _ => throwError "unsupported"
    | _ => throwError "unsupported"
  pushSimple simple

def trExportCmd : Open → M Unit
  | ⟨tgt, none, clauses⟩ => do
    let mut args := #[]
    for c in clauses do
      match c.kind with
      | OpenClause.explicit ns =>
        for n in ns do args := args.push (mkIdent n.kind)
      | _ => throwError "unsupported"
    pushM `(export $(mkIdent tgt.kind):ident ($[$args]*))
  | _ => throwError "unsupported"

def trDeclId (n : Name) (us : LevelDecl) : M Syntax := do
  let us := us.map $ Array.map fun u => mkIdent u.kind
  `(Parser.Command.declId| $(mkIdent n):ident $[.{$[$us],*}]?)

def trTypeSpec (ty : Expr) : M Syntax := do `(Parser.Term.typeSpec| : $(← trExpr ty))
def trOptType (ty : Option Expr) : M (Option Syntax) := ty.mapM trTypeSpec

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
  (bis : Binders) (ty : Option (Spanned Expr)) (val : DeclVal) : M Syntax := do
  let (prio, mods) ← trModifiers mods
  let id ← n.mapM fun n => trDeclId n.kind us
  let sig req := trDeclSig req bis ty
  let val ← match val with
  | DeclVal.expr e => do `(Parser.Command.declValSimple| := $(← trExpr e))
  | DeclVal.eqns #[] => `(Parser.Command.declValSimple| := fun.)
  | DeclVal.eqns arms => `(Parser.Command.declValSimple| := _)
  match dk with
  | DeclKind.abbrev => do `(command| $mods:declModifiers abbrev $id.get! $(← sig false) $val)
  | DeclKind.def => do `(command| $mods:declModifiers def $id.get! $(← sig false) $val)
  | DeclKind.example => do `(command| $mods:declModifiers example $(← sig true) $val)
  | DeclKind.theorem => do `(command| $mods:declModifiers theorem $id.get! $(← sig true) $val)
  | DeclKind.instance => do
    let loc := mkOptionalNode none -- lean 3 doesn't have "local instance"
    let prio ← mkOpt prio fun prio => do
      `(Parser.Command.namedPrio| (priority := $(← trPrio prio)))
    `(command| $mods:declModifiers $loc:attrKind instance $[$id:declId]? $(← sig false) $val)

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
  | Field.notation _, out => throwError "unsupported"

def trFields (flds : Array (Spanned Field)) : M Syntax :=
  @mkNullNode <$> flds.foldlM (fun out fld => trField fld.kind out) #[]

def trStructure (cl : Bool) (mods : Modifiers) (n : Spanned Name) (us : LevelDecl)
  (bis : Binders) (exts : Array (Spanned Parent)) (ty : Option (Spanned Expr))
  (mk : Option (Spanned Mk)) (flds : Array (Spanned Field)) : M Unit := do
  let id ← trDeclId n.kind us
  let bis := mkNullNode $ ← trBinders {} bis
  let exts ← exts.mapM fun
    | ⟨_, _, false, none, ty, #[]⟩ => trExpr ty.kind
    | _ => throwError "unsupported"
  let exts ← mkOpt (if exts.isEmpty then none else some exts) fun exts =>
    `(Parser.Command.extends| extends $[$exts],*)
  let ty ← mkOptionalNode <$> trOptType (ty.map Spanned.kind)
  let flds ← mkOptionalNode <$> match mk, flds with
  | none, #[] => none
  | mk, flds => do
    let mk ← mk.mapM fun ⟨_, _, n, ik⟩ => do
      `(Parser.Command.structCtor| $(mkIdent n.kind):ident $[$(← trInferKind ik)]? ::)
    some $ mkNullNode #[mkAtom "where", mkOptionalNode mk, ← trFields flds]
  push $ mkNode ``Parser.Command.structure #[
    mkAtom (if cl then "class" else "structure"), id, bis, exts, ty, flds, mkOptionalNode none]

def trCommand : Command → M Unit
  | Command.prelude => modify fun s => { s with «prelude» := true }
  | Command.initQuotient => pushM `(init_quot)
  | Command.«import» ns => modify fun s =>
    { s with imports := ns.foldl (fun a n => a.push n.kind) s.imports }
  | Command.mdoc s =>
    push $ mkNode `Lean.Parser.Command.modDocComment #[mkAtom s] -- FIXME: doesn't exist
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
      | _ => throwError "unsupported"
    | _ => throwError "unsupported"
  | Command.decl dk mods n us bis ty val => pushM $ trDecl dk mods n us bis ty val.kind
  | Command.mutualDecl dk mods us bis arms =>
    trMutual arms fun ⟨attrs, n, ty, vals⟩ => do
      trDecl dk mods n us bis ty (DeclVal.eqns vals)
  | Command.inductive cl mods n us bis ty nota intros =>
     pushM $ trInductive cl mods n us bis ty nota intros
  | Command.mutualInductive cl mods us bis nota inds =>
    trMutual inds fun ⟨attrs, n, ty, intros⟩ => do
      trInductive cl mods n us bis ty nota intros
  | Command.structure cl mods n us bis exts ty m flds =>
    trStructure cl mods n us bis exts ty m flds
  | Command.attribute loc _ attrs ns => do
    let kind := if loc then AttributeKind.local else AttributeKind.global
    let attrs := (← trAttributes attrs true kind |>.run {}).2.out
    if attrs.isEmpty || ns.isEmpty then return ()
    let ns := ns.map fun n => mkIdent n.kind
    pushM `(command| attribute [$[$attrs],*] $[$ns]*)
  | Command.precedence sym prec => pure ()
  | Command.notation loc attrs n => throwError "unsupported (TODO)"
  | Command.open true ops => ops.forM trExportCmd
  | Command.open false ops => trOpenCmd ops
  | Command.include true ops => unless ops.isEmpty do
      pushM `(include $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.include false ops => unless ops.isEmpty do
      pushM `(omit $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.hide ops => unless ops.isEmpty do
      pushM `(hide $[$(ops.map fun n => mkIdent n.kind)]*)
  | Command.theory mods => withArray mods 1 fun
    | ⟨_, _, Modifier.noncomputable⟩ => pushM `(command| noncomputable theory)
    | _ => throwError "unsupported"
  | Command.setOption n val => match n.kind, val.kind with
    | `old_structure_cmd, OptionVal.bool b =>
      modifyScope fun s => { s with oldStructureCmd := b }
    | _, _ => throwError "unsupported (TODO)"
  | Command.declareTrace n => throwError "unsupported (TODO)"
  | Command.addKeyEquivalence a b => throwError "unsupported"
  | Command.runCmd e => do pushM `(#eval $(← trExpr e.kind))
  | Command.check e => do pushM `(#check $(← trExpr e.kind))
  | Command.reduce _ e => do pushM `(#reduce $(← trExpr e.kind))
  | Command.eval e => do pushM `(#eval $(← trExpr e.kind))
  | Command.unify e₁ e₂ => throwError "unsupported"
  | Command.compile n => throwError "unsupported"
  | Command.help n => throwError "unsupported"
  | Command.print (PrintCmd.str s) => pushM `(#print $(Syntax.mkStrLit s))
  | Command.print (PrintCmd.ident n) => pushM `(#print $(mkIdent n.kind))
  | Command.print (PrintCmd.axioms (some n)) => pushM `(#print axioms $(mkIdent n.kind))
  | Command.print _ => throwError "unsupported"
  | Command.userCommand n mods args => throwError "unsupported (TODO)"

def AST3toData4 : AST3 → CoreM Data4
  | ⟨commands⟩ => do
    let x := commands.forM fun c => trCommand c.kind
    let (_, s) ← x.run {} |>.run Inhabited.default
    let mut out := #[]
    if s.prelude then out := out.push (← `(prelude))
    for n in s.imports do
      out := out.push (← `(import $(mkIdent n)))
    pure ⟨out ++ s.commands, HashMap.empty⟩

def toIO (x : CoreM α) (env : Environment) : IO α := do
  let coreCtx   : Core.Context := { currNamespace := Name.anonymous, openDecls := [] }
  let coreState : Core.State := { env := env }
  let (result, _) ← x.toIO coreCtx coreState
  pure result

end Translate

def AST3toData4 (ast : AST3) (env : Environment) : IO Data4 := do
  Translate.toIO (Translate.AST3toData4 ast) env
