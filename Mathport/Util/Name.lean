/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

namespace Lean.Name

def mapStrings (f : String → String) : Name → Name
  | anonymous  => anonymous
  | str p s .. => mkStr (mapStrings f p) (f s)
  | num p k .. => mkNum (mapStrings f p) k

def toFilePath (n : Name) : System.FilePath :=
  ⟨"/".intercalate (n.components.map Name.getString!)⟩

end Lean.Name
