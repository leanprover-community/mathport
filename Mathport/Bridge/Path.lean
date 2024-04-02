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
  mod4?   : Option Name
  deriving Inhabited, FromJson, BEq, Hashable, Repr

def Path.toLean3 (cfg : Path.Config) (p : Path) (suffix : String) : FilePath :=
  let l3root := cfg.packages.find! p.package
  let path := l3root / p.mod3.toFilePath
  ⟨path.toString ++ suffix⟩

def Path.mod4 (p : Path) : Name :=
  p.mod4?.getD <| p.mod3.mapStrings String.snake2pascal

def Path.toLean4src (cfg : Path.Config) (p : Path) : FilePath :=
  -- Lib4/lean3/Lean3.lean
  -- Lib4/mathbin/Mathbin.lean
  let path := cfg.outRoot / (FilePath.mk "src") /
    (FilePath.mk p.package.decapitalize) / (FilePath.mk p.package) / p.mod4.toFilePath
  ⟨path.toString ++ ".lean"⟩

def Path.toLean4olean (cfg : Path.Config) (p : Path) : FilePath :=
  let path := cfg.outRoot / (FilePath.mk "oleans") /
    (FilePath.mk p.package.decapitalize) / (FilePath.mk p.package) / p.mod4.toFilePath
  ⟨path.toString ++ ".olean"⟩

def replaceHead : Name → Name → Name
  | .str .anonymous _, n => n
  | .str p s,          n => .str (replaceHead p n) s
  | .num p s,          n => .num (replaceHead p n) s
  | p,                 _ => p

def Path.setMod4 (p : Path) (importRename : NameMap Name) : Path :=
  -- we strip the leading segment `Mathlib.*` because we will prepend the package name `Mathbin.*` later
  { p with mod4? := importRename.find? p.mod3 |>.map (replaceHead · .anonymous) }

def resolveMod3 (cfg : Path.Config) (importRename : NameMap Name) (mod3 : Name) : IO Path := do
  for (package, _) in cfg.packages.toList do
    let path := Path.mk package mod3 none
    if ← (path.toLean3 cfg ".tlean").pathExists then return path.setMod4 importRename
    let path := Path.mk package (mod3 ++ `default) none
    if ← (path.toLean3 cfg ".tlean").pathExists then return path.setMod4 importRename
  throw $ IO.userError s!"[resolveMod3] failed to resolve '{mod3}'"

def parsePath (importRename : NameMap Name) (pmod3 : String) : IO Path := do
  let [pkg, mod3] := pmod3.splitOn "::" | throw (IO.userError "paths must be <pkg>::<mod3>")
  pure <| (Path.mk pkg mod3.toName' none).setMod4 importRename

def parsePaths (importRename : NameMap Name) (pmod3s : List String) : IO (List Path) := do
  pmod3s.mapM (parsePath importRename)

end Mathport
