/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.AST3
import Mathport.Data4

namespace Mathport

open Lean

namespace Translate

open Lean
open Std (HashMap)

structure Context where

structure State where

abbrev TranslateM := ReaderT Context (StateRefT State CoreM)

-- TODO: return Syntax
def AST3toData4 : AST3 → TranslateM Data4 :=
  sorry

def toIO (x : TranslateM α) (env : Environment) : IO α := do
  let coreM : CoreM α := x {} |>.run' {}
  let coreCtx   : Core.Context := { currNamespace := Name.anonymous, openDecls := [] }
  let coreState : Core.State := { env := env }
  let (result, _) ← coreM.toIO coreCtx coreState
  pure result

end Translate

def AST3toData4 (ast : AST3) (env : Environment) : IO Data4 := do
  Translate.toIO (Translate.AST3toData4 ast) env

end Mathport
