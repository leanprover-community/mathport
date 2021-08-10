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

def TacM.run (m : TacM α) (args : Array (Spanned Param)) : M α := do
  let (a, ⟨n⟩) ← (m ⟨args⟩).run {}
  unless args.size = n do throw! "unsupported: too many args"
  a

def next? : TacM (Option Param) := do
  let args := (← read).args
  let i := (← get).pos
  if h : i < args.size then
    modify fun s => { s with pos := i+1 }
    (args.get ⟨i, h⟩).kind
  else none

def next! : TacM Param := do
  match ← next? with | some p => p | none => throw! "missing argument"

def parse (p : Parser.ParserM α) : TacM α := do
  let Param.parse _ args ← next! | throw! "expecting parse arg"
  match p ⟨(← readThe Translate.Context).commands, args⟩ |>.run' 0 with
  | none => throw! "parse error"
  | some a => a

def expr? : TacM (Option AST3.Expr) := do
  match ← next? with
  | none => none
  | some (Param.expr e) => some e.kind
  | _ => throw! "parse error"

def expr! : TacM AST3.Expr := do
  match ← expr? with | some p => p | none => throw! "missing argument"

def itactic : TacM AST3.Block := do
  let Param.block bl ← next! | throw! "expecting tactic arg"
  bl

syntax (name := trTactic) "trTactic " ident+ : attr
syntax (name := trUserNota) "trUserNota " ident+ : attr
syntax (name := trUserAttr) "trUserAttr " ident+ : attr

private def mkExt (name attr : Name) (descr : String) : IO (SimplePersistentEnvExtension (Name × Name) (Array (Name × Name))) := do
  let ext ← registerSimplePersistentEnvExtension {
    name
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (·++·) #[]
  }
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun declName stx attrKind => modifyEnv fun env =>
      stx[1].getArgs.foldl (init := env) fun env stx =>
        ext.addEntry env (stx.getId, declName)
  }
  ext

initialize trTacExtension : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  mkExt `Mathport.Translate.Tactic.trTacExtension `trTactic
    (descr := "lean 3 → 4 tactic translation")

initialize trUserNotaExtension : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  mkExt `Mathport.Translate.Tactic.trUserNotaExtension `trUserNota
    (descr := "lean 3 → 4 user notation translation")

initialize trUserAttrExtension : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  mkExt `Mathport.Translate.Tactic.trUserAttrExtension `trUserAttr
    (descr := "lean 3 → 4 user attribute translation")

elab "trTactics!" : term => do
  let stx ← (trTacExtension.getState (← getEnv)).mapM fun (n3, n4) =>
    `(($(Syntax.mkNameLit s!"`{n3}"):nameLit, $(mkIdent n4):ident))
  Elab.Term.elabTerm (← `(#[$stx,*])) none

elab "trUserNotas!" : term => do
  let stx ← (trUserNotaExtension.getState (← getEnv)).mapM fun (n3, n4) =>
    `(($(Syntax.mkNameLit s!"`{n3}"):nameLit, $(mkIdent n4):ident))
  Elab.Term.elabTerm (← `(#[$stx,*])) none

elab "trUserAttrs!" : term => do
  let stx ← (trUserAttrExtension.getState (← getEnv)).mapM fun (n3, n4) =>
    `(($(Syntax.mkNameLit s!"`{n3}"):nameLit, $(mkIdent n4):ident))
  Elab.Term.elabTerm (← `(#[$stx,*])) none
