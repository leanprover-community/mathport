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

  let mut opts := ({} : Options)
  opts := opts.setBool `pp.analyze false
  opts := opts.setBool `pp.all true

  withImportModulesConst (coreImports ++ extraImports.toList) (opts := opts) (trustLevel := 0) $ λ env => do
    let env := env.setMainModule path.mod4
    let env ← addInitialNameAlignments env -- TODO: store in a prelude .lean file?

    let cmdCtx : Elab.Command.Context := { fileName := path.toLean3 pcfg ".lean" |>.toString, fileMap := dummyFileMap }
    let cmdState : Elab.Command.State := Lean.Elab.Command.mkState env

    CommandElabM.toIO (ctx := cmdCtx) (s := cmdState) do
      -- let _ ← IO.FS.withIsolatedStreams' $ binport1 config path
      binport1 config path
      synport1 config path
      writeModule (← getEnv) $ path.toLean4 pcfg ".olean"

    println! "\n[mathport] END   {path.mod3}\n"

def bindTasks (deps : Array Task) (k? : Option (Unit → IO Task)) : IO Task := do
  if deps.isEmpty then k?.get! () else
  let mut task := deps[0]
  for i in [1:deps.size] do
    task ← bindTaskThrowing task fun () => pure deps[i]
  match k? with
  | none => task
  | some k => bindTaskThrowing task fun () => k ()
where
  bindTaskThrowing (task : Task) (k : Unit → IO Task) : IO Task :=
    IO.bindTask task fun result => match result with
      | Except.ok () => k ()
      | Except.error err => throw err

partial def visit (config : Config) (path : Path) : StateRefT (HashMap Path Task) IO Task := do
  println! "[visit] {repr path}"
  let pcfg := config.pathConfig
  match (← get).find? path with
  | some task => pure task
  | none     => do
    if ← path.toLean4 pcfg ".olean" |>.pathExists then
      println! "[visit] {repr path} already exists"
      IO.asTask (pure ())
    else
      let mut deps := #[]
      for mod3 in ← parseTLeanImports (path.toLean3 pcfg ".tlean") do
        let importPath ← resolveMod3 pcfg mod3
        if config.parallel then
          deps := deps.push (← visit config importPath)
        else
          match ← IO.wait (← visit config importPath) with
          | Except.error err => throw err
          | Except.ok result => deps := deps.push (← IO.asTask $ pure result)
      let task ← bindTasks deps fun () => IO.asTask (mathport1 config path)
      modify λ path2task => path2task.insert path task
      pure task

def mathport (config : Config) (paths : Array Path) : IO Unit := do
  let tasks ← (paths.mapM fun path => visit config path).run' {}
  match ← IO.wait (← bindTasks tasks none) with
  | Except.ok () => println! "[mathport] DONE"
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
