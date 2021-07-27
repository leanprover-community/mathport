/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Binary.Config
import Mathport.Binary.Path

namespace Mathport.Binary

def path34to4 (config : Config) (p : Path34) (suffix : String) : FilePath :=
  (config.outRoot.join p.toLean4).withExtension suffix

def mkPath34 (config : Config) (l4mod : String) (mrpath : FilePath) : Path34 := {
  modInfo := ⟨l4mod, config.modules.find! l4mod⟩,
  mrpath  := mrpath
}

def resolveDotPath3 (config : Config) (dotPath : String) : IO Path34 := do
  let mrpath : FilePath := dot2path dotPath
  for (l4mod, l3path) in config.modules.toList do
    let p34 ← mkPath34 config l4mod mrpath
    if ← p34.toTLean.pathExists then return p34
    let p34 ← mkPath34 config l4mod $ mrpath.join ⟨"default"⟩
    if ← p34.toTLean.pathExists then return p34
  throw $ IO.userError s!"[resolveDotPath3] failed to resolve '{mrpath}'"

end Mathport.Binary
