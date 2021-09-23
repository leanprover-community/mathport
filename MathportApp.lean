import Mathport

open Mathport Lean

unsafe def main (args : List String) : IO Unit := do
  match args with
  | (pathToConfig :: pmod3s@(_ :: _)) =>
    let config ← parseJsonFile Config pathToConfig
    let paths ← parsePaths pmod3s
    println! "[paths] {repr paths}"
    let path := match ← IO.getEnv "LEAN_PATH" with
    | none => []
    | some path => System.SearchPath.parse path
    searchPathRef.set (leanDir! :: "build" :: path)
    mathport config paths.toArray

  | _ => throw $ IO.userError "usage: mathport <path-to-config> [pkg::mod3]+"
