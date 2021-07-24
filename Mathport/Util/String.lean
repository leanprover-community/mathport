/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
namespace String

def snake2camel (snake : String) : String :=
  match snake.splitOn "_" with
  | []          => ""
  | [component] => component
  | first::rest => join $ first :: rest.map capitalize

def snake2pascal (snake : String) : String :=
  join (snake.splitOn "_" |>.map capitalize)

def cmp (x y : String) : Ordering :=
  if x < y then Ordering.lt
  else if x > y then Ordering.gt
  else Ordering.eq

end String
