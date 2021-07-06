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

namespace Translate

open Std (HashMap)
open AST3

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

inductive BinderContext : Type
| bracketedBinder (ty : Bool := false) : BinderContext

def trTacticSeq : Tactic → M Syntax
  | _ => throwError "unsupported (TODO)"

def trExpr : Expr → M Syntax
  | _ => throwError "unsupported (TODO)"

def trBinder : BinderContext → Binder → Array Syntax → M (Array Syntax)
  | BinderContext.bracketedBinder req,
    Binder.binder BinderInfo.instImplicit vars _ (some ty) none, out => do
    let var ← match vars with
    | none => #[]
    | some vars => withArray vars 1 fun v => pure #[mkIdent v.kind, mkAtom ":"]
    out.push $ mkNode ``Parser.Term.instBinder
      #[mkAtom "[", mkNode nullKind var, ← trExpr ty.kind, mkAtom "]"]
  | BinderContext.bracketedBinder req,
    Binder.binder bi (some vars) bis ty dflt, out => do
    let vars := mkNode nullKind $ vars.map fun v => mkIdent v.kind
    let ty := match req, ty with
    | true, none => some Expr.«_»
    | _, _ => ty.map fun ty => ty.kind
    let ty ← mkNode nullKind <$> match ty with
    | none => #[]
    | some ty => do pure #[mkAtom ":", ← trExpr ty]
    if bi == BinderInfo.implicit then
      out.push $ mkNode ``Parser.Term.implicitBinder #[mkAtom "(", vars, ty, mkAtom ")"]
    else
      let dflt ← mkNode nullKind <$> match dflt with
      | none => #[]
      | some (Default.«:=» e) => do
        #[mkNode ``Parser.Term.binderDefault #[mkAtom ":=", ← trExpr e.kind]]
      | some (Default.«.» e) => do
        #[mkNode ``Parser.Term.binderTactic #[mkAtom ":=", mkAtom "by",
          ← trTacticSeq $ Tactic.expr $ e.map Expr.ident]]
      out.push $ mkNode ``Parser.Term.explicitBinder #[mkAtom "(", vars, ty, dflt, mkAtom ")"]
  | BinderContext.bracketedBinder _, _, _ => throwError "unsupported"

def trBinders (bc : BinderContext) (bis : Array (Spanned Binder)) : M (Array Syntax) := do
  bis.foldlM (fun out bi => trBinder bc bi.kind out) #[]

def trOpenCmd (ops : Array Open) : M Unit := do
  let mut simple := #[]
  for o in ops do
    match o with
    | ⟨tgt, none, clauses⟩ =>
      if clauses.isEmpty then
        simple := simple.push (mkIdent tgt.kind)
      else
        pushSimple simple
        simple := #[]
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
          -- pushM `(open $(mkIdent tgt) ($[$(explicit.map fun n => mkIdent n.kind)]*))
          push $ mkNode ``Parser.Command.open #[mkAtom "open",
            mkNode ``Parser.Command.openOnly #[
              mkIdent tgt.kind, mkAtom "(",
              mkNode nullKind $ explicit.map fun n => mkIdent n.kind,
              mkAtom ")"]]
        | true, false, true =>
          push $ mkNode ``Parser.Command.open #[mkAtom "open",
            mkNode ``Parser.Command.openRenaming #[
              mkIdent tgt.kind, mkAtom "renaming",
              mkNode nullKind $ mkSepArray
                (renames.map fun ⟨a, b⟩ =>
                  mkNode ``Parser.Command.openRenamingItem #[
                    mkIdent a.kind, mkAtom "→", mkIdent b.kind])
                (mkAtom ",")]]
        | true, true, false =>
          push $ mkNode ``Parser.Command.open #[mkAtom "open",
            mkNode ``Parser.Command.openHiding #[
              mkIdent tgt.kind, mkAtom "hiding",
              mkNode nullKind $ hides.map fun n => mkIdent n.kind]]
        | _, _, _ => throwError "unsupported"
    | _ => throwError "unsupported"
  pushSimple simple
where
  pushSimple (s : Array Syntax) := do
    unless s.isEmpty do
      -- pushM `(open $[$(s)]*)
      push $ mkNode ``Parser.Command.open #[mkAtom "open",
        mkNode ``Parser.Command.openSimple s]

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

def trCommand : Command → M Unit
  | Command.prelude => modify fun s => { s with «prelude» := true }
  | Command.initQuotient => pushM `(init_quot)
  | Command.«import» ns => modify fun s =>
    { s with imports := ns.foldl (fun a n => a.push n.kind) s.imports }
  | Command.mdoc s => pure () -- FIXME
  | Command.«universe» _ _ ns =>
    pushM `(universe $[$(ns.map fun n => mkIdent n.kind)]*)
  | Command.«namespace» n => do
    pushScope; pushM `(namespace $(mkIdent n.kind))
  | Command.«section» n => do
    pushScope; pushM `(section $[$(n.map fun n => mkIdent n.kind)]?)
  | Command.«end» n => do
    popScope; pushM `(end $[$(n.map fun n => mkIdent n.kind)]?)
  | Command.«variable» vk _ _ bis => do
    unless bis.isEmpty do
      let bis ← trBinders BinderContext.bracketedBinder bis
      match vk with
      | VariableKind.variable =>
        -- pushM `(variable $[$bis]+)
        push $ mkNode ``Parser.Command.variable #[mkAtom "variable", mkNode nullKind bis]
      | VariableKind.parameter =>
        -- pushM `(parameter $[$bis]+)
        push $ mkNode ``parameterCmd #[mkAtom "parameter", mkNode nullKind bis]
  | Command.axiom ak mods n us bis ty => throwError "unsupported (TODO)"
  | Command.axioms ak mods bis => throwError "unsupported (TODO)"
  | Command.decl dk mods n us bis ty val => throwError "unsupported (TODO)"
  | Command.mutualDecl dk mods us bis arms => throwError "unsupported (TODO)"
  | Command.inductive cl mods n us bis ty nota intros => throwError "unsupported (TODO)"
  | Command.mutualInductive cl mods us bis nota inds => throwError "unsupported (TODO)"
  | Command.structure cl mods n us bis exts ty m flds => throwError "unsupported (TODO)"
  | Command.attribute loc mods attrs ns => throwError "unsupported (TODO)"
  | Command.precedence sym prec => throwError "unsupported (TODO)"
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
    | ⟨_, _, Modifier.noncomputable⟩ => pure ()
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
