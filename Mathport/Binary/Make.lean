/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Mathport.Util.System
import Mathport.Util.Parse
import Mathport.Util.Import
import Mathport.Binary.Basic
import Mathport.Binary.Path
import Mathport.Binary.Config
import Mathport.Binary.ParseTLean
import Mathport.Binary.Apply
import Mathport.Binary.PathUtil

namespace Mathport.Binary.Make

open Lean in
def genOLeanFor (config : Config) (path34 : Path34) : IO Unit := do
  println! s!"\n[genOLeanFor] START {path34.mrpath}\n"
  createDirectoriesIfNotExists (path34to4 config path34 "olean").toString

  let coreImports  : List Import  := [{ module := `Init : Import }]
  let extraImports : Array Import ← (← parseTLeanImports (path34.toLean3 "tlean")).mapM fun dp => do
    let import ← (← resolveDotPath3 config dp).toLean4dot.toName
    println! "[import] {import}"
    pure { module := import }

  withImportModulesConst (coreImports ++ extraImports.toList) (opts := {}) (trustLevel := 0) $ λ env₀ => do
    let env₀ := env₀.setMainModule (path2dot path34.mrpath)
    let nameInfoMap : HashMap Name NameInfo := {} -- TODO: stitch together from imports
    discard <| BinportM.toIO (ctx := { config := config, path34 := path34 }) (env := env₀) (nameInfoMap := nameInfoMap) do
      let mods ← parseTLean (path34.toLean3 "tlean")
      for mod in mods do applyModification mod
      writeModule (← getEnv) $ path34to4 config path34 "olean"
      println! "\n[genOLeanFor] END   {path34.mrpath}\n"

abbrev Job := Task (Except IO.Error Unit)

structure Context where
  config : Config

structure State where
  path2task : HashMap String Job := {}

abbrev RunM := ReaderT Context (StateRefT State IO)

partial def visit (target : Path34) : RunM Job := do
  match (← get).path2task.find? target.toTLean.toString with
  | some task => pure task
  | none      => do
    if ← path34to4 (← read).config target "olean" |>.pathExists then
      IO.asTask (pure ())
    else
      let mut jobs := #[]
      for dotPath in ← parseTLeanImports (target.toLean3 "tlean") do
        let path34 ← resolveDotPath3 (← read).config dotPath
        jobs := jobs.push (← visit path34)
      for job in jobs do
        match ← IO.wait job with
        | Except.ok _ => pure ()
        | Except.error err => throw err
      let job ← IO.asTask $ genOLeanFor (← read).config target
      modify λ s => { s with path2task := s.path2task.insert target.toTLean.toString job }
      pure job

end Make

open Make in
def make (config : Config) (l4mod mrpath : String) : IO Unit := do
  let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
  println! "[searchPath] {LEAN_PATH}"
  Lean.initSearchPath LEAN_PATH
  let target := mkPath34 config l4mod mrpath
  let job ← (visit target) { config := config } |>.run' (s := {})
  let result ← IO.wait job
  match result with
  | Except.ok _ => pure ()
  | Except.error err => throw err

end Mathport.Binary
