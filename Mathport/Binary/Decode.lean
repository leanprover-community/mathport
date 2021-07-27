/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Binary.RenameExt

namespace Mathport.Binary

open Lean

-- Awkward: this section refers to names that are created during the port

def decodeChar (e : Expr) : MetaM Char := do
  let char34 := (getRenameMap (← getEnv)).find! `char
  if e.isAppOfArity (char34 ++ `mk) 2 then
    match (e.getArg! 0).natLit? with
    | some n => Char.ofNat n
    | _ => throwError "[decodeChar] failed on {e}"
  else
    throwError "[decodeChar] failed on {e}"

partial def decodeStringCore (e : Expr) : MetaM String := do
  let list34 := (getRenameMap (← getEnv)).find! `list
  if e.isAppOfArity (list34 ++ `nil) 1 then
    ""
  else if e.isAppOfArity (list34 ++ `cons) 3 then
    let s ← decodeStringCore (e.getArg! 2)
    let c ← decodeChar (e.getArg! 1)
    pure ⟨c :: s.data⟩
  else
    throwError "[decodeStringCore] failed on {e}"

def decodeUnsigned (e : Expr) : MetaM Nat := do
  let fin34 := (getRenameMap (← getEnv)).find! `fin
  if e.isAppOfArity (fin34 ++ `mk) 2 then
    match (e.getArg! 0).natLit? with
    | some n => n
    | _ => throwError "[decodeUInt32] failed on {e}"
  else
    throwError "[decodeUInt32] failed on {e}"

def decodeString (e : Expr) : MetaM String := do
  let stringImp34 := (getRenameMap (← getEnv)).find! `string_imp
  if e.isAppOfArity (stringImp34 ++ `mk) 1 then
    decodeStringCore (e.getArg! 0)
  else throwError "[decodeString] failed on {e}"

partial def decodeName (e : Expr) : MetaM Name := do
  let name34 := (getRenameMap (← getEnv)).find! `name
  if e.isAppOfArity (name34 ++ `anonymous) 0 then
    Name.anonymous
  else if e.isAppOfArity (name34 ++ `mk_string) 2 then
    Name.mkStr (← decodeName (e.getArg! 1)) (← decodeString (e.getArg! 0))
  else if e.isAppOfArity (name34 ++ `mk_numeral) 2 then
    Name.mkNum (← decodeName (e.getArg! 1)) (← decodeUnsigned (e.getArg! 0))
  else
    throwError "[decodeName] failed on {e}"

end Mathport.Binary
