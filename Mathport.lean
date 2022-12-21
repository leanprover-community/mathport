/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathport.Binary
import Mathport.Syntax

-- We import all of mathlib here so that `lake build` keeps the `Mathlib.olean` up to date.
import Mathlib

namespace Mathport

open Lean Lean.Elab.Command

def mathport1 (config : Config) (path : Path) : IO Unit := do
  let pcfg := config.pathConfig

  createDirectoriesIfNotExists (path.toLean4olean pcfg).toString
  createDirectoriesIfNotExists (path.toLean4src pcfg).toString

  IO.eprintln s!"porting {path.mod4}"

  println! s!"\n[mathport] START {path.mod3}\n"

  let mut imports : Array Import ← (← parseTLeanImports (path.toLean3 pcfg ".tlean")).mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg mod3
    pure { module := ipath.package ++ ipath.mod4 : Import }

  if imports.isEmpty then imports := config.baseModules.map ({ module := · : Import })
  imports := imports ++ config.extraModules.map ({ module := · : Import })

  let opts := ({} : Options)
    |>.setNat `maxRecDepth 2000
    |>.setNat `maxHeartbeats 800000
    |>.setBool `pp.rawOnError true

  try
    withImportModulesConst imports.toList (opts := opts) (trustLevel := 0) $ λ env => do
      let env := env.setMainModule path.mod4
      let cmdCtx : Elab.Command.Context := {
        fileName := path.toLean3 pcfg ".lean" |>.toString
        fileMap := dummyFileMap
        tacticCache? := none
      }
      let cmdState : Elab.Command.State := Lean.Elab.Command.mkState (env := env) (opts := opts)

      CommandElabM.toIO (ctx := cmdCtx) (s := cmdState) do
        -- let _ ← IO.FS.withIsolatedStreams' $ binport1 config path
        binport1 config path
        synport1 config path
        writeModule (← getEnv) $ path.toLean4olean pcfg

      println! "\n[mathport] END   {path.mod3}\n"
  catch err =>
    throw $ IO.userError s!"failed to port {path.package}:{path.mod4} with imports {imports.toList}:\n{err}"

end Mathport
