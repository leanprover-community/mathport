/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Prelude
import Mathport.Binary
import Mathport.Syntax

namespace Mathport

open Lean Lean.Elab.Command

abbrev Task := _root_.Task (Except IO.Error Unit)

def mathport1 (config : Config) (path : Path) : IO Unit := do
  let pcfg := config.pathConfig

  println! s!"\n[mathport] START {path.mod3}\n"
  createDirectoriesIfNotExists (path.toLean4 pcfg ".olean").toString

  let mut imports : Array Import ← (← parseTLeanImports (path.toLean3 pcfg ".tlean")).mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg mod3
    { module := ipath.package ++ ipath.mod4 : Import }

  if imports.isEmpty then imports := #[{ module := `Mathport.Prelude : Import }]

  let opts := ({} : Options) |>.setNat `maxRecDepth 2000

  withImportModulesConst imports.toList (opts := opts) (trustLevel := 0) $ λ env => do
    let env := env.setMainModule path.mod4
    let cmdCtx : Elab.Command.Context := { fileName := path.toLean3 pcfg ".lean" |>.toString, fileMap := dummyFileMap }
    let cmdState : Elab.Command.State := Lean.Elab.Command.mkState (env := env) (opts := opts)

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
