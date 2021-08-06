/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Binary
import Mathport.Syntax

namespace Mathport

open Lean Lean.Elab.Command

abbrev Task := _root_.Task (Except IO.Error Unit)

def mathport1 (config : Config) (path : Path) : IO Unit := do
  let pcfg := config.pathConfig

  println! s!"\n[mathport] START {path.mod3}\n"
  createDirectoriesIfNotExists (path.toLean4 pcfg ".olean").toString

  let coreImports  : List Import  := [{ module := `Mathport.Syntax.Prelude : Import }]
  let extraImports : Array Import ← (← parseTLeanImports (path.toLean3 pcfg ".tlean")).mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg mod3
    { module := ipath.package ++ ipath.mod4 : Import }

  let opts := ({} : Options).setBool `pp.all true

  withImportModulesConst (coreImports ++ extraImports.toList) (opts := opts) (trustLevel := 0) $ λ env => do
    let env := env.setMainModule path.mod4
    let env ← addInitialNameAlignments env -- TODO: store in a prelude .lean file?

    let cmdCtx : Elab.Command.Context := { fileName := path.toLean3 pcfg ".lean" |>.toString, fileMap := dummyFileMap }
    let cmdState : Elab.Command.State := Lean.Elab.Command.mkState env

    CommandElabM.toIO (ctx := cmdCtx) (s := cmdState) do
      binport1 config path
      synport1 config path
      writeModule (← getEnv) $ path.toLean4 pcfg ".olean"

    println! "\n[mathport] END   {path.mod3}\n"

partial def visit (config : Config) (path : Path) : StateRefT (HashMap Path Task) IO Task := do
  println! "[visit] {repr path}"
  let pcfg := config.pathConfig
  match (← get).find? path with
  | some task => pure task
  | none     => do
    if ← path.toLean4 pcfg "olean" |>.pathExists then
      IO.asTask (pure ())
    else
      let mut importTasks := #[]
      for mod3 in ← parseTLeanImports (path.toLean3 pcfg ".tlean") do
        let importPath ← resolveMod3 pcfg mod3
        importTasks := importTasks.push (← visit config importPath)
      -- TODO: we wait rather than bind since there was a memory leak at some point
      for importTask in importTasks do
        match ← IO.wait importTask with
        | Except.ok _ => pure ()
        | Except.error err => throw err
      let task ← IO.asTask $ mathport1 config path
      modify λ path2task => path2task.insert path task
      pure task

def mathport (config : Config) (paths : Array Path) : IO Unit := core.run' {} where
  core : StateRefT (HashMap Path Task) IO Unit := do
    let mut tasks := #[]
    for path in paths do
      tasks := tasks.push (← visit config path)
    for task in tasks do
      let result ← IO.wait task
      match result with
      | Except.ok _ => pure ()
      | Except.error err => throw err

end Mathport

open Mathport

unsafe def main (args : List String) : IO Unit := do
  match args with
  | (pathToConfig :: pmod3s@(_ :: _)) =>
    let config ← parseJsonFile Config pathToConfig
    let paths ← parsePaths pmod3s
    println! "[paths] {repr paths}"
    let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
    Lean.initSearchPath LEAN_PATH
    mathport config paths.toArray

  | _ => throw $ IO.userError "usage: mathport <path-to-config> [pkg::mod3]+"

where
  parsePaths pmod3s : IO (List Path) := do
    pmod3s.mapM fun pmod3 => do
      let [pkg, mod3] ← pure (pmod3.splitOn "::") | throw (IO.userError "paths must be <pkg>::<mod3>")
      pure $ Path.mk pkg mod3.toName
