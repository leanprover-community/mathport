/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean
import Mathport.Util.Path
import Mathport.Util.System
import Mathport.Util.Import
import Mathport.Util.Parse
import Mathport.Util.RenameExt
import Mathport.Syntax.AST3
import Mathport.Syntax.Data4
import Mathport.Syntax.Parse
import Mathport.Syntax.Translate

namespace Mathport.Syntax

namespace Make

open Lean
open Translate

def genLeanFor (pcfg : Path.Config) (path : Path) : IO Unit := do
  println! s!"\n[genLeanFor] START {path.mod3}\n"
  createDirectoriesIfNotExists (path.toLean4 pcfg "syn.lean").toString

  let coreImports : List Import  := [{ module := `Init : Import }]
  let ipaths ← (← parseTLeanImports (path.toLean3 pcfg "tlean")).mapM (resolveMod3 pcfg)
  let extraImports : Array Import := ipaths.map fun ipath => { module := ipath.package ++ ipath.mod4 : Import }

  let opts := ({} : Options)

  withImportModulesConst (coreImports ++ extraImports.toList) (opts := opts) (trustLevel := 0) $ λ binportEnv => do
    let binportEnv := binportEnv.setMainModule path.mod4
    let binportEnv ← addInitialNameAlignments binportEnv

    let mut auxData := AuxData.initial
    for ipath in ipaths do auxData ← auxData.merge $ ipath.toLean4 pcfg "aux.json"

    -- TODO: expose IO interface elsewhere. More of synport will end up being in CoreM-extending monads.
    let coreCtx   : Core.Context := {}
    -- TODO: the binport env will not be able to parenthesize the module in general.
    -- Synport needs to produce an environment that can parenthesize it.
    let coreState : Core.State := { env := binportEnv }

    let ast3 ← parseAST3 $ path.toLean3 pcfg "ast.json"
    let ⟨⟨⟨fmt, _⟩, finalAuxData⟩, _⟩ ← Core.CoreM.toIO (ctx := coreCtx) (s := coreState) do
      Mathport.AST3toData4 (getRenameMap binportEnv) ast3 |>.run auxData
    finalAuxData.export $ path.toLean4 pcfg "aux.json"
    IO.FS.writeFile (path.toLean4 pcfg "syn.lean") (toString fmt)
    println! "\n[genLeanFor] END   {path.mod3}\n"

abbrev Job := Task (Except IO.Error Unit)

structure State where
  path2task : HashMap Path Job := {}

partial def visit (pcfg : Path.Config) (target : Path) : StateRefT State IO Job := do
  match (← get).path2task.find? target with
  | some task => pure task
  | none      => do
    if ← target.toLean4 pcfg "syn.lean" |>.pathExists then
      IO.asTask (pure ())
    else
      let mut jobs := #[]
      for mod3 in ← parseTLeanImports (target.toLean3 pcfg "tlean") do
        let ipath ← resolveMod3 pcfg mod3
        jobs := jobs.push (← visit pcfg ipath)
      for job in jobs do
        match ← IO.wait job with
        | Except.ok _ => pure ()
        | Except.error err => throw err
      let job ← IO.asTask $ genLeanFor pcfg target
      modify λ s => { s with path2task := s.path2task.insert target job }
      pure job

end Make

def main (args : List String) : IO Unit := do
  match args with
  | [package, mod3, pathToConfig] =>
    let pcfg ← parseJsonFile Path.Config pathToConfig
    let target := Path.mk package mod3.toName
    let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
    println! "[searchPath] {LEAN_PATH}"
    Lean.initSearchPath LEAN_PATH
    let job ← (Make.visit pcfg target) |>.run' (s := {})
    let result ← IO.wait job
    match result with
    | Except.ok _ => pure ()
    | Except.error err => throw err

  | _ => throw $ IO.userError "usage: mathport binary <lean4mod> <lean3mrp> <path-to-config>"


end Mathport.Syntax
