/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Mathlib.Data.List.EditDistance.Defs
import Mathport.Binary
import Mathport.Syntax

namespace Mathport

open Lean Lean.Elab.Command

def _root_.Array.minBy? [Ord β] (arr : Array α) (f : α → β) : Option α :=
  let _ : Ord α := ⟨fun a b => compare (f a) (f b)⟩
  arr.min?

-- We allow imports to be aligned in many-to-many fashion using `#align_import`, but
-- mathport can't actually handle merging files, so we sanitize the state to ensure a
-- perfect matching here. We use Levenshtein distance to prefer more similar names
-- to handle the case where file A is merged into a different file B which already
-- has a B alignment.
def getImportRename (config : Config) : IO (NameMap Name) := do
  let imports := (config.baseModules ++ config.extraModules).map ({ module := · : Import })
  try
    withImportModulesConst imports (opts := {}) (trustLevel := 0) fun env => do
      let mut toMod4 := {}
      let quality (mod3 mod4 : Name) := levenshtein (δ := Nat) default
        (mod3.mapStrings String.snake2pascal).toString.toList mod4.toString.toList
      -- This is super nasty, but we need to drop the Environment at the end of this function
      -- in order to avoid using gobs of memory, but this also invalidates all lean objects
      -- referencing things in the Environment so we have to make sure to deep copy everything
      -- we have to pass out of the function or else we will get segfaults.
      let rec externalize : Name → Name
        | .anonymous => .anonymous
        | .num p n => .num (externalize p) n
        | .str p n => .str (externalize p) (n.append "")
      for arr in (Mathlib.Prelude.Rename.renameImportExtension.getState env).extern do
        let arr := arr.filter (!toMod4.contains ·.2.mod3)
        let some (mod4, _) := arr.get? 0 | continue
        let some (_, {mod3, ..}) := arr.minBy? (fun (_, e) => quality e.mod3 mod4) | continue
        if if let some mod4' := toMod4.find? mod3 then (quality mod3 mod4).blt (quality mod3 mod4')
          else true
        then toMod4 := toMod4.insert (externalize mod3) (externalize mod4)
      return ShareCommon.shareCommon toMod4
  catch _ => throw $ IO.userError "failed to load import rename state"

def mathport1 (config : Config) (importRename : NameMap Name) (path : Path) : IO Unit := do
  let pcfg := config.pathConfig

  createDirectoriesIfNotExists (path.toLean4olean pcfg).toString
  createDirectoriesIfNotExists (path.toLean4src pcfg).toString

  IO.eprintln s!"porting {path.mod4}"

  println! s!"\n[mathport] START {path.mod3}\n"

  let imports3 ← parseTLeanImports (path.toLean3 pcfg ".tlean") path.mod3
  let mut imports : Array Import ← imports3.mapM fun mod3 => do
    let ipath : Path ← resolveMod3 pcfg importRename mod3
    pure { module := ipath.package ++ ipath.mod4 : Import }

  if imports.isEmpty then imports := config.baseModules.map ({ module := · : Import })
  imports := imports ++ config.extraModules.map ({ module := · : Import })

  let opts := ({} : Options)
    |>.setNat `maxRecDepth 2000
    |>.setNat `maxHeartbeats 50000
    |>.setBool `pp.rawOnError true

  try
    withImportModulesConst imports (opts := opts) (trustLevel := 0) $ λ env => do
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
        synport1 config importRename path imports3
        writeModule (← getEnv) $ path.toLean4olean pcfg

      println! "\n[mathport] END   {path.mod3}\n"
  catch err =>
    throw $ IO.userError
      s!"failed to port {path.package}:{path.mod4} with imports {imports.toList}:\n{err}"

end Mathport
