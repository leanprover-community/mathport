/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Util.Json

namespace Mathport.Binary

open Lean
open Std (HashMap)

inductive ClashKind
  | foundDefEq : ClashKind
  | freshDecl  : ClashKind
  deriving Inhabited, Repr, BEq

structure NameInfo where
  name4     : Name
  clashKind : ClashKind
  deriving Inhabited, Repr

abbrev NameInfoMap := HashMap Name NameInfo

end Mathport.Binary
