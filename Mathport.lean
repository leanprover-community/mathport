/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Environment
import Mathport.AST3
import Mathport.Parse
import Mathport.Data4
import Mathport.Translate
import Mathport.Refine

-- TODO: process entire library in parallel
unsafe def main (args : List String) : IO Unit := do
  match args with
  | [filename] => do
    let ast3 ← Mathport.parseAST3 ⟨filename⟩
    -- println! "{repr ast3}"
    -- Mathport.withEnvironmentFor ⟨filename⟩ (opts := {}) (trustLevel := 0) fun env => do
      -- TODO: stay in CoreM between these two?
      -- let data4 ← Mathport.AST3toData4 ast3 env
      -- let stx ← Mathport.refineSyntax data4 env
      -- TODO: write syntax to file
    pure ()

  | _ => throw $ IO.userError "usage: ./mathport <filename>"
