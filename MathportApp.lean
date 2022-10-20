import Mathport

open Mathport Lean

abbrev VisitResult := Task (Except IO.Error Unit)

partial def visit (pathToConfig : String) (config : Config) (path : Path) :
    StateT (HashMap Path VisitResult) IO VisitResult := do
  println! "[visit] {repr path}"
  let pcfg := config.pathConfig
  if let some task := (← get).find? path then return task
  if ← path.toLean4olean pcfg |>.pathExists then
    return Task.pure (Except.ok ())
  let deps ← (← parseTLeanImports (path.toLean3 pcfg ".tlean")).mapM
    fun mod3 => do visit pathToConfig config (← resolveMod3 pcfg mod3)
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
    let path ← parsePath pmod3
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    mathport1 config path

  | ("--make" :: pathToConfig :: pmod3s@(_ :: _)) =>
    let config ← parseJsonFile Config pathToConfig
    let paths ← parsePaths pmod3s
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    let results := (← (paths.mapM (visit pathToConfig config)).run' {}).map (·.get)
    let errors := results.filterMap fun | .error err => some err | _ => none
    unless errors.isEmpty do
      errors.forM (IO.eprintln ·)
      IO.Process.exit 1

  | _ =>
    IO.eprintln "usage: mathport [--make] <path-to-config> [pkg::mod3]"
    IO.Process.exit 1
