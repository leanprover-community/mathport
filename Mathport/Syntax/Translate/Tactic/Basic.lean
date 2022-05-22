/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.Parser

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport
namespace Translate

open AST3 Parser

namespace Tactic

structure Context where
  args : Array (Spanned Param)

structure State where
  pos : Nat := 0

abbrev TacM := ReaderT Context $ StateT State M

def TacM.run (m : TacM α) (name : Name) (args : Array (Spanned Param)) : M α := do
  let (a, ⟨n⟩) ← (m ⟨args⟩).run {}
  unless args.size = n do
    warn! "unsupported: too many args: {name} ... {(repr <| args.extract n args.size).pretty 999999}"
  pure a

def next? : TacM (Option Param) := do
  let args := (← read).args
  let i := (← get).pos
  if h : i < args.size then
    modify fun s => { s with pos := i+1 }
    pure (args.get ⟨i, h⟩).kind
  else pure none

def next! : TacM Param := do
  match ← next? with | some p => pure p | none => warn! "missing argument"

def parse (p : Parser.ParserM α) : TacM α := do
  let Param.parse _ args ← next! | throw! "expecting parse arg"
  p.run' args

def parse_0 (t : TacM α) := parse (pure ()) *> t

def expr? : TacM (Option (Spanned AST3.Expr)) := do
  match ← next? with
  | none => pure none
  | some (Param.expr e) => pure e
  | _ => warn! "parse error"

def expr! : TacM (Spanned AST3.Expr) := do
  match ← expr? with | some p => pure p | none => warn! "missing argument"

def itactic : TacM AST3.Block := do
  let Param.block bl ← next! | warn! "expecting tactic arg"
  pure bl

def withNoMods (tac : TacM α) : Modifiers → TacM α
  | #[] => tac
  | _ => warn! "expecting no modifiers" | tac

def tagAttr (n : Name) : TacM Syntax := parse_0 $ pure (mkSimpleAttr n)

scoped instance : Coe (TacM α) (Modifiers → TacM α) := ⟨withNoMods⟩

def withDocString (tac : Option String → TacM α) : Modifiers → TacM α
  | #[] => tac none
  | #[⟨_, Modifier.doc s⟩] => tac (some s)
  | _ => warn! "unsupported modifiers in user command" | tac none

scoped instance : Coe (Option String → TacM α) (Modifiers → TacM α) := ⟨withDocString⟩
scoped instance : Coe (α → TacM Syntax) (α → TacM Unit) := ⟨fun tac mods => do push (← tac mods)⟩

abbrev NameExt := SimplePersistentEnvExtension (Name × Name) (NameMap Name)

private def mkExt (name attr : Name) (descr : String) : IO NameExt := do
  let addEntryFn | m, (n3, n4) => m.insert n3 n4
  let ext ← registerSimplePersistentEnvExtension {
    name, addEntryFn
    addImportedFn := mkStateFromImportedEntries addEntryFn {}
  }
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun declName stx attrKind => do
      let s := ext.getState (← getEnv)
      let ns ← stx[1].getArgs.mapM fun stx => do
        let n := stx.getId
        if s.contains n then throwErrorAt stx "translation for {n} already declared"
        pure n
      modifyEnv $ ns.foldl fun env n =>
        ext.addEntry env (n, declName)
  }
  pure ext

private def mkElab (ext : NameExt) (ty : Lean.Expr) : Elab.Term.TermElabM Lean.Expr := do
  let mut stx := #[]
  for (n3, n4) in ext.getState (← getEnv) do
    stx := stx.push $ ← `(($(Quote.quote n3), $(mkIdent n4):ident))
  Elab.Term.elabTerm (← `(#[$stx,*])) (some ty)

syntax (name := trTactic) "trTactic " ident+ : attr
syntax (name := trNITactic) "trNITactic " ident+ : attr
syntax (name := trConv) "trConv " ident+ : attr
syntax (name := trUserNota) "trUserNota " ident+ : attr
syntax (name := trUserAttr) "trUserAttr " ident+ : attr
syntax (name := trUserCmd) "trUserCmd " ident+ : attr

initialize trTacExtension : NameExt ←
  mkExt `Mathport.Translate.Tactic.trTacExtension `trTactic
    (descr := "lean 3 → 4 interactive tactic translation")
initialize trNITacExtension : NameExt ←
  mkExt `Mathport.Translate.Tactic.trNITacExtension `trNITactic
    (descr := "lean 3 → 4 noninteractive tactic translation")
initialize trConvExtension : NameExt ←
  mkExt `Mathport.Translate.Tactic.trConvExtension `trConv
    (descr := "lean 3 → 4 interactive conv tactic translation")
initialize trUserNotaExtension : NameExt ←
  mkExt `Mathport.Translate.Tactic.trUserNotaExtension `trUserNota
    (descr := "lean 3 → 4 user notation translation")
initialize trUserAttrExtension : NameExt ←
  mkExt `Mathport.Translate.Tactic.trUserAttrExtension `trUserAttr
    (descr := "lean 3 → 4 user attribute translation")
initialize trUserCmdExtension : NameExt ←
  mkExt `Mathport.Translate.Tactic.trUserCmdExtension `trUserCmd
    (descr := "lean 3 → 4 user attribute translation")

elab "trTactics!" : term <= ty => mkElab trTacExtension ty
elab "trNITactics!" : term <= ty => mkElab trNITacExtension ty
elab "trConvs!" : term <= ty => mkElab trConvExtension ty
elab "trUserNotas!" : term <= ty => mkElab trUserNotaExtension ty
elab "trUserAttrs!" : term <= ty => mkElab trUserAttrExtension ty
elab "trUserCmds!" : term <= ty => mkElab trUserCmdExtension ty
