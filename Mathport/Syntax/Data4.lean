/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Util.Misc

namespace Mathport
open Lean

structure Data4 where
  fmt : Format
  exprs : HashMap Position Expr
  deriving Inhabited

end Mathport
