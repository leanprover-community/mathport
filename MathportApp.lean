import Mathport

open Mathport Lean

abbrev VisitResult := Task (Except IO.Error Unit)

partial def visit (pathToConfig : String) (config : Config)
    (importRename : NameMap Name) (path : Path) :
    StateT (HashMap Path VisitResult) IO VisitResult := do
  println! "[visit] {repr path}"
  let pcfg := config.pathConfig
  if let some task := (← get).find? path then return task
  if ← path.toLean4olean pcfg |>.pathExists then
    return Task.pure (Except.ok ())
  let deps ← (← parseTLeanImports (path.toLean3 pcfg ".tlean") path.mod3).mapM
    fun mod3 => do visit pathToConfig config importRename (← resolveMod3 pcfg importRename mod3)
  let task ← IO.mapTasks (tasks := deps.toList) fun deps => do
    for dep in deps do if let .error err := dep then throw err
    let proc ← IO.Process.spawn {
      cmd := (← IO.appPath).toString
      args := #[pathToConfig, s!"{path.package}::{path.mod3}"]
    }
    if (← proc.wait) != 0 then throw <| IO.userError s!"Failed to port {repr path}"
  modify (·.insert path task)
  return task

def main (args : List String) : IO Unit := do
  match args with
  | [pathToConfig, pmod3] =>
    let config ← parseJsonFile Config pathToConfig
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    let importRename ← getImportRename config
    let path ← parsePath importRename pmod3
    mathport1 config importRename path

  | "--make" :: pathToConfig :: pmod3s@(_ :: _) =>
    let config ← parseJsonFile Config pathToConfig
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    let importRename ← getImportRename config
    let paths ← parsePaths importRename pmod3s
    let results := (← (paths.mapM (visit pathToConfig config importRename)).run' {}).map (·.get)
    let errors := results.filterMap fun | .error err => some err | _ => none
    unless errors.isEmpty do
      errors.forM (IO.eprintln ·)
      IO.Process.exit 1

  | _ =>
    IO.eprintln "usage: mathport [--make] <path-to-config> [pkg::mod3]"
    IO.Process.exit 1
