/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Bridge.Rename

namespace Mathport.Binary

open Lean

-- Awkward: this section refers to names that are created during the port

def decodeChar (e : Expr) : MetaM Char := do
  let char34 := Rename.resolveIdent! (← getEnv) `char
  if e.isAppOfArity (char34 ++ `mk) 2 then
    match (e.getArg! 0).natLit? with
    | some n => pure $ Char.ofNat n
    | _ => throwError "[decodeChar] failed on {e}"
  else
    throwError "[decodeChar] failed on {e}"

partial def decodeStringCore (e : Expr) : MetaM String := do
  let list34 := Rename.resolveIdent! (← getEnv) `list
  if e.isAppOfArity (list34 ++ `nil) 1 then
    pure ""
  else if e.isAppOfArity (list34 ++ `cons) 3 then
    let s ← decodeStringCore (e.getArg! 2)
    let c ← decodeChar (e.getArg! 1)
    pure ⟨c :: s.data⟩
  else
    throwError "[decodeStringCore] failed on {e}"

def decodeUnsigned (e : Expr) : MetaM Nat := do
  let fin34 := Rename.resolveIdent! (← getEnv) `fin
  if e.isAppOfArity (fin34 ++ `mk) 2 then
    match (e.getArg! 0).natLit? with
    | some n => pure n
    | _ => throwError "[decodeUInt32] failed on {e}"
  else
    throwError "[decodeUInt32] failed on {e}"

def decodeString (e : Expr) : MetaM String := do
  let stringImp34 := Rename.resolveIdent! (← getEnv) `string_imp
  if e.isAppOfArity (stringImp34 ++ `mk) 1 then
    decodeStringCore (e.getArg! 0)
  else throwError "[decodeString] failed on {e}"

partial def decodeName (e : Expr) : MetaM Name := do
  let name34 := Rename.resolveIdent! (← getEnv) `name
  if e.isAppOfArity (name34 ++ `anonymous) 0 then
    return Name.anonymous
  if e.isAppOfArity (name34 ++ `mk_string) 2 then
    return Name.mkStr (← decodeName (e.getArg! 1)) (← decodeString (e.getArg! 0))
  if e.isAppOfArity (name34 ++ `mk_numeral) 2 then
    return Name.mkNum (← decodeName (e.getArg! 1)) (← decodeUnsigned (e.getArg! 0))
  throwError "[decodeName] failed on {e}"

end Mathport.Binary
