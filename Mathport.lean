/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Binary
import Mathport.Syntax

-- TODO: process entire library in parallel
unsafe def main (args : List String) : IO Unit := do
  match args with
  | ("binary"::args) => do Mathport.Binary.main args
  | ("syntax"::args) => do Mathport.Syntax.main args
  | _ => throw $ IO.userError "usage: mathport [binary|syntax] ..."
