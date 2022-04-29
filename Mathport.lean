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

  IO.eprintln s!"porting {path.mod4}"

  println! s!"\n[mathport] START {path.mod3}\n"

  let mut imports : Array Import ← (← parseTLeanImports (path.toLean3 pcfg ".tlean")).mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg mod3
    pure { module := ipath.package ++ ipath.mod4 : Import }

  if imports.isEmpty then imports := #[{ module := `Mathlib : Import }]

  let opts := ({} : Options)
    |>.setNat `maxRecDepth 2000
    |>.setNat `maxHeartbeats 400000
    |>.setBool `pp.rawOnError true

  try
    withImportModulesConst imports.toList (opts := opts) (trustLevel := 0) $ λ env => do
      let env := env.setMainModule path.mod4
      let cmdCtx : Elab.Command.Context := { fileName := path.toLean3 pcfg ".lean" |>.toString, fileMap := dummyFileMap }
      let cmdState : Elab.Command.State := Lean.Elab.Command.mkState (env := env) (opts := opts)

      CommandElabM.toIO (ctx := cmdCtx) (s := cmdState) do
        -- let _ ← IO.FS.withIsolatedStreams' $ binport1 config path
        binport1 config path
        synport1 config path
        writeModule (← getEnv) $ path.toLean4olean pcfg

      println! "\n[mathport] END   {path.mod3}\n"
  catch err =>
    throw $ IO.userError s!"failed to port {path.package}:{path.mod4} with imports {imports.toList}:\n{err}"

def bindTasks (deps : Array Task) (k? : Option (Unit → IO Task)) : IO Task := do
  if deps.isEmpty then k?.getD (fun _ => pure $ Task.pure (Except.ok ())) () else
  let mut task := deps[0]
  for i in [1:deps.size] do
    task ← bindTaskThrowing task fun () => pure deps[i]
  match k? with
  | none => pure task
  | some k => bindTaskThrowing task fun () => k ()
where
  bindTaskThrowing (task : Task) (k : Unit → IO Task) : IO Task :=
    IO.bindTask task fun result => match result with
      | Except.ok () => k ()
      | Except.error err => throw err

partial def visit (config : Config) (path : Path) (topLevel := false) : StateRefT (HashMap Path Task) IO Task := do
  println! "[visit] {repr path}"
  let pcfg := config.pathConfig
  match (← get).find? path with
  | some task => pure task
  | none     => do
    if !topLevel && (← path.toLean4olean pcfg |>.pathExists) then
      pure $ Task.pure (Except.ok ())
    else
      let mut deps := #[]
      for mod3 in ← parseTLeanImports (path.toLean3 pcfg ".tlean") do
        let importPath ← resolveMod3 pcfg mod3
        deps := deps.push (← visit config importPath)
      createDirectoriesIfNotExists (path.toLean4olean pcfg).toString
      createDirectoriesIfNotExists (path.toLean4src pcfg).toString
      let task ← bindTasks deps (some fun () => IO.asTask (mathport1 config path))
      unless config.parallel do
        if let Except.error err ← IO.wait task then
          throw err
      modify λ path2task => path2task.insert path task
      pure task

def mathport (config : Config) (paths : Array Path) : IO Unit := do
  let tasks ← (paths.mapM fun path => visit config path (topLevel := true)).run' {}
  match ← IO.wait (← bindTasks tasks none) with
  | Except.ok () => println! "[mathport] DONE"
  | Except.error err => throw err

end Mathport
