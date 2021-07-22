/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean
import Mathport.Util.Misc
import Mathport.Util.Json

open Lean
open System (FilePath)

namespace Mathport.Binary

-- Example: data.nat.basic
structure DotPath where
  path : String
  deriving Inhabited, Repr, FromJson

-- Example: data/nat/basic
structure ModRelPath where
  path   : FilePath
  deriving Inhabited, Repr, FromJson

def DotPath.toModRelPath (p : DotPath) : ModRelPath :=
  ⟨System.mkFilePath $ p.path.splitOn "."⟩

def ModRelPath.toDotPath (p : ModRelPath) : DotPath :=
  ⟨".".intercalate $ p.path.components⟩

-- Example: Mathlib mathlib/src
structure ModuleInfo where
  l4name : FilePath
  l3path : FilePath
  deriving Inhabited, Repr, FromJson

structure Path34 where
  modInfo : ModuleInfo
  mrpath  : ModRelPath
  deriving Inhabited, Repr, FromJson

def Path34.toLean3 (p : Path34) (suffix : String) : FilePath :=
  (p.modInfo.l3path.join p.mrpath.path).withExtension suffix

def Path34.toTLean (p : Path34) : FilePath :=
  p.toLean3 "tlean"

def Path34.toLean4dot (p : Path34) : String :=
  ".".intercalate [p.modInfo.l4name.toString, p.mrpath.toDotPath.path]

end Mathport.Binary
