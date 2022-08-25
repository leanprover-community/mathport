import Mathport.Syntax.Parse
open Mathport

def main (args : List String) : IO Unit := do
  for fileName in args do
    let (ast3, tacticInvocations) ← parseAST3 fileName
    IO.println (repr ast3)
    for ti in tacticInvocations do IO.println (repr ti)