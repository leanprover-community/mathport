/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
open Lean

@[implemented_by withImportModules]
opaque withImportModulesConst (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) (x : Environment → IO α) : IO α
