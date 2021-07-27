/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
namespace String

def snake2pascalCamel (snake : String) (lc : Bool) : String := do
  let mut pascal := join (snake.splitOn "_" |>.map capitalize)
  if lc then pascal := decapitalize pascal
  if snake.startsWith "_" then pascal := "_" ++ pascal
  if snake.endsWith "_" then pascal := pascal ++ "_"
  pascal

def snake2pascal (snake : String) : String :=
  snake2pascalCamel snake (lc := false)

def snake2camel (snake : String) : String :=
  snake2pascalCamel snake (lc := true)

def cmp (x y : String) : Ordering :=
  if x < y then Ordering.lt
  else if x > y then Ordering.gt
  else Ordering.eq

end String
