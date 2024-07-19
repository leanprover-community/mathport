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
  | ["--build-align", pathToConfig, out1, out2] =>
    let config ← parseJsonFile Config pathToConfig
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    let writeArray (file : FilePath) (arr : Array (String × String)) : IO Unit := do
      let arr := arr.qsort (·.1 < ·.1)
      let h ← IO.FS.Handle.mk file IO.FS.Mode.write
      for _h : i in [:arr.size] do
        let (n3, n4) := arr[i]
        h.putStr <| s!"\
          {if i = 0 then "{" else " "}\
          {Json.renderString n3}: {Json.renderString n4}\
          {if i+1=arr.size then "}" else ","}\n"
    withConfigEnv config fun env => do
      let mut importRename := #[]
      for (n3, n4) in ← getImportRename env do
        importRename := importRename.push (toString n3, toString n4)
      writeArray out1 importRename
      let mut renames := #[]
      let toLean4 := (Mathlib.Prelude.Rename.renameExtension.getState env).get.toLean4
      for (name3, _, name4) in toLean4 do
        renames := renames.push (toString name3, toString name4)
      writeArray out2 renames

  | [pathToConfig, pmod3] =>
    let config ← parseJsonFile Config pathToConfig
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    let importRename ← withConfigEnv config getImportRename
    let path ← parsePath importRename pmod3
    mathport1 config importRename path

  | "--make" :: pathToConfig :: pmod3s@(_ :: _) =>
    let config ← parseJsonFile Config pathToConfig
    searchPathRef.set (lean_dir% :: config.pathConfig.leanPath)
    let importRename ← withConfigEnv config getImportRename
    let paths ← parsePaths importRename pmod3s
    let results := (← (paths.mapM (visit pathToConfig config importRename)).run' {}).map (·.get)
    let errors := results.filterMap fun | .error err => some err | _ => none
    unless errors.isEmpty do
      errors.forM (IO.eprintln ·)
      IO.Process.exit 1

  | _ =>
    IO.eprintln "usage: mathport [--make] <path-to-config> [pkg::mod3]"
    IO.Process.exit 1
