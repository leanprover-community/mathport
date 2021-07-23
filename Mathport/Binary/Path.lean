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

def dot2path (dot : String) : FilePath :=
  System.mkFilePath $ dot.splitOn "."

def path2dot (p : FilePath) : String :=
  ".".intercalate $ p.components

structure ModuleInfo where
  l4mod  : String
  l3root : FilePath
  deriving Inhabited, Repr, FromJson

structure Path34 where
  modInfo : ModuleInfo
  mrpath  : FilePath -- "module-relative path"
  deriving Inhabited, Repr, FromJson

def Path34.toLean3 (p : Path34) (suffix : String) : FilePath :=
  (p.modInfo.l3root.join p.mrpath).withExtension suffix

def Path34.toTLean (p : Path34) : FilePath :=
  p.toLean3 "tlean"

def Path34.toLean4dot (p : Path34) : String :=
  ".".intercalate [p.modInfo.l4mod, path2dot p.mrpath]

end Mathport.Binary
