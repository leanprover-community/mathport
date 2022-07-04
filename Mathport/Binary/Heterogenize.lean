/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Util.String
import Mathport.Binary.Basic
import Mathport.Binary.Number
import Mathport.Binary.Decode
import Mathport.Binary.TranslateName

namespace Mathport.Binary

open Lean Lean.Meta

structure HBinInfo where
  hName    : Name
  instName : Name

def hBinMap : HashMap Name HBinInfo :=
  let m : HashMap Name HBinInfo := {}
  let m := m.insert `Add.add ⟨`HAdd.hAdd, `instHAdd⟩
  let m := m.insert `Sub.sub ⟨`HSub.hSub, `instHSub⟩
  let m := m.insert `Mul.mul ⟨`HMul.hMul, `instHMul⟩
  let m := m.insert `Div.div ⟨`HDiv.hDiv, `instHDiv⟩
  let m := m.insert `Mod.mod ⟨`HMod.hMod, `instHMod⟩
  m

def heterogenize (e : Expr) : MetaM Expr := Meta.transform e (post := core)
/-
@instHAdd.{u_1} : {α : Type u_1} → [inst : Add.{u_1} α] → HAdd.{u_1, u_1, u_1} α α α
@Add.add.{0} Nat Nat.hasAdd Nat.zero Nat.zero : Nat
@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
  (@instHAdd_2.{0, 0} Nat Nat <Add.{u_1} α>)
  Nat.zero Nat.zero : Nat
-/
where
  core (e : Expr) : MetaM TransformStep := do
    e.withApp fun f args => do
      if !f.isConst then return TransformStep.done e
      match hBinMap.find? f.constName! with
      | some ⟨hName, instName⟩ =>
        if args.size < 2 then return TransformStep.done e
        let lvl := f.constLevels!.head!
        let type := args[0]!
        let inst := args[1]!
        let inst' := mkAppN (mkConst instName [lvl]) #[type, inst]
        let rest := args.extract 2 args.size
        let e' := mkAppN (mkConst hName [lvl, lvl, lvl]) (#[type, type, type, inst'] ++ rest)
        return TransformStep.done e'

      | none =>
        if f.isConstOf `Pow.pow && args.size ≥ 3 then
          let [lvl1, lvl2] := f.constLevels! | throwError "Pow.pow should have 2 levels"
          -- (@instHPow.{0, 0} Nat Nat instPowNatNat)
          let instName := `instHPow
          let (type1, type2) := (args[0]!, args[1]!)
          let inst  := args[2]!
          let inst' := mkAppN (mkConst instName [lvl1, lvl2]) #[type1, type2, inst]
          let rest := args.extract 3 args.size
          let e' := mkAppN (mkConst `HPow.hPow [lvl1, lvl2, lvl1]) (#[type1, type2, type1, inst'] ++ rest)
          return TransformStep.done e'
        else return TransformStep.done e


end Mathport.Binary
