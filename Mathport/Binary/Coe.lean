/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Based off <lean4>/src/Lean/Meta/Coe.lean
-/
import Lean
import Mathport.Bridge.RenameExt

namespace Mathport.Binary

open Lean Lean.Meta

structure CoeInfo where
  instPos      : Nat
  indName      : Name
  projPos      : Nat

def isCoeApp? (e : Expr) : Option CoeInfo :=
  let nArgs := e.getAppNumArgs
  -- Note: this hardcodes the Lean4 translations
  -- (either call the rename map or make sure this stays in sync)
  if e.isAppOf `coe' && nArgs ≥ 4 then some ⟨2, `HasLiftT, 0⟩
  else if e.isAppOf `coeSort' && nArgs ≥ 3 then some ⟨1, `HasCoeToSort, 1⟩
  else if e.isAppOf `coeFn && nArgs ≥ 3 then some ⟨1, `HasCoeToFun, 1⟩
  else none

partial def expandCoe (e : Expr) : MetaM Expr :=
  transform e (pre := step)
where
  step (e : Expr) : MetaM TransformStep := do
    match isCoeApp? e with
    | none => TransformStep.visit e
    | some ⟨instPos, indName, projPos⟩ =>
      let args := e.getAppArgs
      -- TODO: do we really need to try/catch here? Or increase # heartbeats?
      let fn := mkProj indName projPos args[instPos]
      let newFn ← withCurrHeartbeats $ withTransparency TransparencyMode.all $
        reduce fn (explicitOnly := false) (skipTypes := false) (skipProofs := false)
      let mut newArgs := #[args[instPos+1]]
      for i in [instPos+2:args.size] do newArgs := newArgs.push args[i]
      -- TODO: confirm that we need only apply this once in the `coeFn` case
      let e' := (mkAppN newFn newArgs).headBeta
      -- TODO: pp.maxDepth = <small>?
      -- println! "[coe.reduce] {← ppExpr fn} ==> {← ppExpr newFn}"
      -- println! "[coe] {← ppExpr e} ==> {← ppExpr e'}"
      TransformStep.visit e'

end Mathport.Binary
