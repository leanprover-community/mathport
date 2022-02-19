import Mathport

open Mathport Lean

unsafe def main (args : List String) : IO Unit := do
  match args with
  | (pathToConfig :: pmod3s@(_ :: _)) =>
    let config ← parseJsonFile Config pathToConfig
    let paths ← parsePaths pmod3s
    println! "[paths] {repr paths}"
    searchPathRef.set (leanDir! :: config.pathConfig.leanPath)
    mathport config paths.toArray

  | _ => throw $ IO.userError "usage: mathport <path-to-config> [pkg::mod3]+"
