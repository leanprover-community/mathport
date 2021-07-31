/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Util.System
import Mathport.Binary.Basic
import Mathport.Binary.Apply
import Mathport.Binary.RenameExt
import Mathport.Binary.Config
import Mathport.Binary.ParseTLean

namespace Mathport.Binary

namespace Make

open Lean

def genOLeanFor (config : Config) (path : Path) : IO Unit := do
  let pcfg := config.pathConfig

  println! s!"\n[genOLeanFor] START {path.mod3}\n"
  createDirectoriesIfNotExists (path.toLean4 pcfg "olean").toString

  let coreImports  : List Import  := [{ module := `Init : Import }]
  let extraImports : Array Import ← (← parseTLeanImports (path.toLean3 pcfg "tlean")).mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg mod3
    { module := ipath.package ++ ipath.mod4 : Import }

  let opts := ({} : Options).setBool `pp.all true

  withImportModulesConst (coreImports ++ extraImports.toList) (opts := opts) (trustLevel := 0) $ λ env => do
    let env := env.setMainModule path.mod4
    let env ← addInitialNameAlignments env
    discard <| BinportM.runIO (ctx := { config := config, path := path }) (env := env) do
      let mods ← parseTLean (path.toLean3 pcfg "tlean")
      for mod in mods do applyModification mod
      writeModule (← getEnv) $ path.toLean4 pcfg "olean"
      println! "\n[genOLeanFor] END   {path.mod3}\n"

abbrev Job := Task (Except IO.Error Unit)

structure Context where
  config : Config

structure State where
  path2task : HashMap Path Job := {}

abbrev MakeM := ReaderT Context (StateRefT State IO)

partial def visit (target : Path) : MakeM Job := do
  let pcfg := (← read).config.pathConfig
  match (← get).path2task.find? target with
  | some task => pure task
  | none      => do
    if ← target.toLean4 pcfg "olean" |>.pathExists then
      IO.asTask (pure ())
    else
      let mut jobs := #[]
      for mod3 in ← parseTLeanImports (target.toLean3 pcfg "tlean") do
        let ipath ← resolveMod3 pcfg mod3
        jobs := jobs.push (← visit ipath)
      for job in jobs do
        match ← IO.wait job with
        | Except.ok _ => pure ()
        | Except.error err => throw err
      let job ← IO.asTask $ genOLeanFor (← read).config target
      modify λ s => { s with path2task := s.path2task.insert target job }
      pure job

end Make

def main (args : List String) : IO Unit := do
  match args with
  | [package, mod3, pathToConfig] =>
    let config ← parseJsonFile Config pathToConfig
    let target := Path.mk package mod3.toName
    let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
    println! "[searchPath] {LEAN_PATH}"
    Lean.initSearchPath LEAN_PATH
    let job ← (Make.visit target) { config := config } |>.run' (s := {})
    let result ← IO.wait job
    match result with
    | Except.ok _ => pure ()
    | Except.error err => throw err

  | _ => throw $ IO.userError "usage: mathport binary <lean4mod> <lean3mrp> <path-to-config>"

end Mathport.Binary
