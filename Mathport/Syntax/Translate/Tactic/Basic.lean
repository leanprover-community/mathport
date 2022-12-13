/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Basic
import Mathport.Syntax.Translate.Parser
import Mathlib.Mathport.Syntax

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

instance : Warnable (Spanned AST3.Expr) where
  warn s := ⟨default, .string s⟩

instance : Warnable Block where
  warn _ := default

instance : Warnable Param where
  warn _ := .block default

def next! : TacM Param := do
  match ← next? with | some p => pure p | none => warn! "missing argument"

def parse (p : Parser.ParserM α) : TacM α := do
  let Param.parse _ args ← next! | throw! "expecting parse arg"
  p.run' args

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

structure Parse1 (α) := run : TacM α

def parse1 (p : Parser.ParserM α) (f : α → M β) : Parse1 β := ⟨do f (← parse p)⟩
def parse0 (x : M α) : Parse1 α := parse1 (pure ()) fun _ => x

def tagAttr (n : Name) : Parse1 Syntax.Attr := parse0 <| pure (mkSimpleAttr n)

def withNoMods (tac : Parse1 α) : Modifiers → Parse1 α
  | #[] => tac
  | _ => ⟨warn! "expecting no modifiers" | tac.run⟩

scoped instance : Coe (Parse1 α) (Modifiers → Parse1 α) := ⟨withNoMods⟩

def withDocString (tac : Option String → Parse1 α) : Modifiers → Parse1 α
  | #[] => tac none
  | #[⟨_, Modifier.doc s⟩] => tac (some s)
  | _ => ⟨warn! "unsupported modifiers in user command" | (tac none).run⟩

scoped instance : Coe (Option String → Parse1 α) (Modifiers → Parse1 α) := ⟨withDocString⟩
scoped instance : Coe (α → Parse1 Syntax.Command) (α → Parse1 Unit) :=
  ⟨fun tac mods => ⟨do push (← (tac mods).run)⟩⟩

open Qq
abbrev NameExt (_α : Q(Type)) :=
  SimplePersistentEnvExtension (Name × Name) (NameMap Name)

open Meta Elab Term in
private def mkExt (attr : Name) (descr : String)
    (name : Name := by exact decl_name%) : IO (NameExt α) := do
  let addEntryFn m | (n3, n4) => m.insert n3 n4
  let ext ← registerSimplePersistentEnvExtension {
    name, addEntryFn
    addImportedFn := mkStateFromImportedEntries addEntryFn {}
  }
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun declName stx attrKind => do
      let s := ext.getState (← getEnv)
      _ ← MetaM.run' <| TermElabM.run' <| Lean.Elab.Term.ensureHasType α (.const declName [])
      let ns ← stx[1].getArgs.mapM fun stx => do
        let n := stx.getId
        if s.contains n then throwErrorAt stx "translation for {n} already declared"
        pure n
      modifyEnv $ ns.foldl fun env n =>
        ext.addEntry env (n, declName)
  }
  pure ext

private def mkElab (ext : NameExt α) : Elab.Term.TermElabM Lean.Expr := do
  let mut stx := #[]
  let m ← α.toSyntax
  for (n3, n4) in ext.getState (← getEnv) do
    stx := stx.push $ ← `(($(Quote.quote n3), ($(mkIdent n4):ident : $m)))
  Elab.Term.elabTerm (← `(#[$stx,*])) q(Array (Name × $α))

syntax (name := tr_tactic) "tr_tactic " ident+ : attr
syntax (name := tr_ni_tactic) "tr_ni_tactic " ident+ : attr
syntax (name := tr_conv) "tr_conv " ident+ : attr
syntax (name := tr_user_nota) "tr_user_nota " ident+ : attr
syntax (name := tr_user_attr) "tr_user_attr " ident+ : attr
syntax (name := tr_user_cmd) "tr_user_cmd " ident+ : attr

initialize trTacExtension : NameExt q(TacM Syntax.Tactic) ←
  mkExt `tr_tactic "lean 3 → 4 interactive tactic translation"
initialize trNITacExtension : NameExt q(AST3.Expr → M Syntax.Tactic) ←
  mkExt `tr_ni_tactic "lean 3 → 4 noninteractive tactic translation"
initialize trConvExtension : NameExt q(TacM Syntax.Conv) ←
  mkExt `tr_conv "lean 3 → 4 interactive conv tactic translation"
initialize trUserNotaExtension : NameExt q(TacM Syntax.Term) ←
  mkExt `tr_user_nota "lean 3 → 4 user notation translation"
initialize trUserAttrExtension : NameExt q(Parse1 Syntax.Attr) ←
  mkExt `tr_user_attr "lean 3 → 4 user attribute translation"
initialize trUserCmdExtension : NameExt q(Modifiers → Parse1 Unit) ←
  mkExt `tr_user_cmd "lean 3 → 4 user attribute translation"

elab "tr_tactics%" : term => mkElab trTacExtension
elab "tr_ni_tactics%" : term => mkElab trNITacExtension
elab "tr_convs%" : term => mkElab trConvExtension
elab "tr_user_notas%" : term => mkElab trUserNotaExtension
elab "tr_user_attrs%" : term => mkElab trUserAttrExtension
elab "tr_user_cmds%" : term => mkElab trUserCmdExtension
