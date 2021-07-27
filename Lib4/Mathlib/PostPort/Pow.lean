/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean3.Init.Core

universe u v
variable {α : Type u} {β : Type v}

noncomputable instance [HasPow α β] : HPow α β α := ⟨HasPow.pow⟩
noncomputable instance [HasPow α α] : Pow α      := ⟨HasPow.pow⟩
