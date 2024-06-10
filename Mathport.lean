/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathlib.Data.List.EditDistance.Defs
import Lake.Load.Elab
import Mathport.Binary
import Mathport.Syntax

namespace Mathport

open Lean Lean.Elab.Command

def _root_.Array.minBy? [Ord β] (arr : Array α) (f : α → β) : Option α :=
  let _ : Ord α := ⟨fun a b => compare (f a) (f b)⟩
  arr.min?

section «Workaround for lean4#3826»

initialize importModuleDataCache : IO.Ref (HashMap Name (ModuleData × CompactedRegion)) ← IO.mkRef {}

partial def importModulesCore' (imports : Array Import) : ImportStateM Unit := do
  for i in imports do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      continue
    modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
    let (mod, region) ← (do
      if let some res := (← importModuleDataCache.get).find? i.module then
        return res
      let mFile ← findOLean i.module
      unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
      let res ← readModuleData mFile
      importModuleDataCache.modify (·.insert i.module res)
      return res)
    importModulesCore' mod.imports
    modify fun s => { s with
      moduleData  := s.moduleData.push mod
      regions     := s.regions.push region
      moduleNames := s.moduleNames.push i.module
    }

def importModules' (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (leakEnv := false) : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    let (_, s) ← importModulesCore' imports |>.run
    finalizeImport (leakEnv := leakEnv) s imports opts trustLevel

/-- Like `importModules`, but fetch the resulting import state from the cache if possible. -/
def importModulesUsingCache' (imports : Array Import) (opts : Options) (trustLevel : UInt32) : IO Environment := do
  if let some env := (← Lake.importEnvCache.get).find? imports then
    return env
  let env ← importModules' imports opts trustLevel
  Lake.importEnvCache.modify (·.insert imports env)
  return env

end «Workaround for lean4#3826»

-- We allow imports to be aligned in many-to-many fashion using `#align_import`, but
-- mathport can't actually handle merging files, so we sanitize the state to ensure a
-- perfect matching here. We use Levenshtein distance to prefer more similar names
-- to handle the case where file A is merged into a different file B which already
-- has a B alignment.
def getImportRename (config : Config) : IO (NameMap Name) := do
  let imports := (config.baseModules ++ config.extraModules).map ({ module := · : Import })
  try
    let env ← importModulesUsingCache' imports (opts := {}) (trustLevel := 0)
    let mut toMod4 := {}
    let quality (mod3 mod4 : Name) := levenshtein (δ := Nat) default
      (mod3.mapStrings String.snake2pascal).toString.toList mod4.toString.toList
    for arr in (Mathlib.Prelude.Rename.renameImportExtension.getState env).extern do
      let arr := arr.filter (!toMod4.contains ·.2.mod3)
      let some (mod4, _) := arr.get? 0 | continue
      let some (_, {mod3, ..}) := arr.minBy? (fun (_, e) => quality e.mod3 mod4) | continue
      if if let some mod4' := toMod4.find? mod3 then (quality mod3 mod4).blt (quality mod3 mod4')
        else true
      then toMod4 := toMod4.insert mod3 mod4
    return toMod4
  catch e => throw $ IO.userError s!"failed to load import rename state: {e.toString}"

def mathport1 (config : Config) (importRename : NameMap Name) (path : Path) : IO Unit := do
  let pcfg := config.pathConfig

  createDirectoriesIfNotExists (path.toLean4olean pcfg).toString
  createDirectoriesIfNotExists (path.toLean4src pcfg).toString

  IO.eprintln s!"porting {path.mod4}"

  println! s!"\n[mathport] START {path.mod3}\n"

  let imports3 ← parseTLeanImports (path.toLean3 pcfg ".tlean") path.mod3
  let mut imports : Array Import ← imports3.mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg importRename mod3
    pure { module := .appendCore (.mkSimple ipath.package) ipath.mod4 : Import }

  if imports.isEmpty then imports := config.baseModules.map ({ module := · : Import })
  imports := imports ++ config.extraModules.map ({ module := · : Import })

  let opts := ({} : Options)
    |>.setNat `maxRecDepth 2000
    |>.setNat `maxHeartbeats 50000
    |>.setBool `pp.rawOnError true

  try
    let env ← importModulesUsingCache' imports (opts := opts) (trustLevel := 0)
    let env := env.setMainModule path.mod4
    let cmdCtx : Elab.Command.Context := {
      fileName := path.toLean3 pcfg ".lean" |>.toString
      fileMap := dummyFileMap
      tacticCache? := none
      snap? := none
      cancelTk? := none
    }
    let cmdState : Elab.Command.State := Lean.Elab.Command.mkState (env := env) (opts := opts)

    CommandElabM.toIO (ctx := cmdCtx) (s := cmdState) do
      -- let _ ← IO.FS.withIsolatedStreams' $ binport1 config path
      binport1 config path
      synport1 config importRename path imports3
      writeModule (← getEnv) $ path.toLean4olean pcfg

    println! "\n[mathport] END   {path.mod3}\n"
  catch err =>
    throw $ IO.userError
      s!"failed to port {path.package}:{path.mod4} with imports {imports.toList}:\n{err}"

end Mathport
