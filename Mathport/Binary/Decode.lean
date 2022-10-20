/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Bridge.Rename

namespace Mathport.Binary

open Lean Meta

-- Awkward: this section refers to names that are created during the port

def decodeChar (e : Expr) : MetaM Char := do
  let e ← whnf e
  let char34 := Rename.resolveIdent! (← getEnv) `char true
  if e.isAppOfArity (char34 ++ `mk) 2 then
    if let some n := (← whnf (e.getArg! 0)).natLit? then
      return Char.ofNat n
  throwError "[decodeChar] failed on {e}"

def decodeUnsigned (e : Expr) : MetaM Nat := do
  let fin34 := Rename.resolveIdent! (← getEnv) `fin true
  let e ← whnf e
  if e.isAppOfArity (fin34 ++ `mk) 2 then
    if let some n := (← whnf (e.getArg! 0)).natLit? then
      return n
  throwError "[decodeUInt32] failed on {e}"

partial def decodeString (e : Expr) : MetaM String := do
  let stringStr34 := Rename.resolveIdent! (← getEnv) `string.str true
  let stringEmpty34 := Rename.resolveIdent! (← getEnv) `string.empty true
  if e.isAppOfArity stringStr34 2 then
    return (← decodeString (e.getArg! 0)).push (← decodeChar (e.getArg! 1))
  else if e.isConstOf stringEmpty34 then
    return ""
  throwError "[decodeString] failed on {e}"

partial def decodeName (e : Expr) : MetaM Name := do
  let name34 := Rename.resolveIdent! (← getEnv) `name true
  let e ← whnf e
  if e.isAppOfArity (name34 ++ `anonymous) 0 then
    return Name.anonymous
  if e.isAppOfArity (name34 ++ `mk_string) 2 then
    return Name.mkStr (← decodeName (e.getArg! 1)) (← decodeString (e.getArg! 0))
  if e.isAppOfArity (name34 ++ `mk_numeral) 2 then
    return Name.mkNum (← decodeName (e.getArg! 1)) (← decodeUnsigned (e.getArg! 0))
  throwError "[decodeName] failed on {e}"

end Mathport.Binary
