/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean3.Init.Coe

universe u v
variable {α : Sort u} {β : Sort v}

noncomputable instance hasCoe [inst : HasCoe α β] : Coe α β := {
  coe := @HasCoe.coe _ _ inst
}

-- TODO: why does mathlib declare these instances directly?
-- topology/algebra/open_subgroup.lean:42:instance has_coe_set : has_coe_t (open_subgroup G) (set G) := ⟨λ U, U.1⟩
noncomputable instance hasCoeT [inst : HasCoeT α β] : CoeTC α β := {
  coe := @HasCoeT.coe _ _ inst
}

noncomputable instance hasCoeToFun [inst : HasCoeToFun α] : CoeFun α (no_index (@HasCoeToFun.F _ inst)) := {
  coe := @HasCoeToFun.coe _ inst
}

noncomputable instance hasCoeToSort [inst : HasCoeToSort α] : CoeSort α (no_index (@HasCoeToSort.S _ inst)) := {
  coe := @HasCoeToSort.coe _ inst
}
