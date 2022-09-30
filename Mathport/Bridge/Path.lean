/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Utilities for managing paths.
-/
import Mathport.Util.Json
import Mathport.Util.Name
import Mathport.Bridge.Rename

namespace Mathport

open Lean
open System (FilePath)

def dot2path (dot : String) : FilePath :=
  System.mkFilePath $ dot.splitOn "."

structure Path.Config where
  outRoot  : FilePath := ""
  packages : HashMap String FilePath := {} -- "Mathlib" -> <mathlib3>/src
  leanPath : List FilePath := []
  deriving Inhabited, FromJson

structure Path where
  package : String
  mod3    : Name
  deriving Inhabited, FromJson, BEq, Hashable, Repr

def Path.toLean3 (cfg : Path.Config) (p : Path) (suffix : String) : FilePath :=
  let l3root := cfg.packages.find! p.package
  let path := l3root / p.mod3.toFilePath
  ⟨path.toString ++ suffix⟩

def Path.mod4 (p : Path) : Name :=
  p.mod3.mapStrings String.snake2pascal

def Path.toLean4src (cfg : Path.Config) (p : Path) : FilePath :=
  -- Lib4/lean3/Lean3.lean
  -- Lib4/mathbin/Mathbin.lean
  let path := cfg.outRoot / (FilePath.mk "src") / (FilePath.mk p.package.decapitalize) / (FilePath.mk p.package) / p.mod4.toFilePath
  ⟨path.toString ++ ".lean"⟩

def Path.toLean4olean (cfg : Path.Config) (p : Path) : FilePath :=
  let path := cfg.outRoot / (FilePath.mk "oleans") / (FilePath.mk p.package.decapitalize) / (FilePath.mk p.package) / p.mod4.toFilePath
  ⟨path.toString ++ ".olean"⟩

def resolveMod3 (cfg : Path.Config) (mod3 : Name) : IO Path := do
  for (package, _) in cfg.packages.toList do
    let path := Path.mk package mod3
    if ← (path.toLean3 cfg ".tlean").pathExists then return path
    let path := Path.mk package (mod3 ++ `default)
    if ← (path.toLean3 cfg ".tlean").pathExists then return path
  throw $ IO.userError s!"[resolveMod3] failed to resolve '{mod3}'"

-- For both binport and synport
def Rename.renameModule (pcfg : Path.Config) (mod3 : Name) : IO Name := do
  let ipath : Path ← resolveMod3 pcfg mod3
  pure $ ipath.package ++ ipath.mod4

def parsePath (pmod3 : String) : IO Path := do
  let [pkg, mod3] := pmod3.splitOn "::" | throw (IO.userError "paths must be <pkg>::<mod3>")
  pure $ Path.mk pkg mod3.toName

def parsePaths (pmod3s : List String) : IO (List Path) := do
  pmod3s.mapM parsePath

end Mathport
