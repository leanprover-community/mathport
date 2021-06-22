/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Std.Data.HashMap
import Std.Data.RBMap

namespace Lean

deriving instance FromJson for Position
deriving instance Hashable for Position

def dummyFileMap : FileMap := ⟨"", #[0], #[1]⟩

end Lean

export Std (HashSet HashMap RBMap RBNode)
export System (FilePath)
