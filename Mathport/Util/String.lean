/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
namespace String

def snake2pascalCamel (snake : String) (lc : Bool) : String := Id.run do
  let mut pascal := join (snake.splitOn "_" |>.map capitalize)
  if lc then pascal := decapitalize pascal
  if snake.startsWith "_" then pascal := "_" ++ pascal
  if snake.endsWith "_" then pascal := pascal ++ "_"
  pascal

def snake2pascal (snake : String) : String :=
  -- pre-empt collisions in category theory where the original is already pascal case
  if (snake.get 0).isUpper && !snake.contains '_' && !snake.all Char.isUpper then snake ++ "Cat"
  else snake2pascalCamel snake (lc := false)

def snake2camel (snake : String) : String :=
  snake2pascalCamel snake (lc := true)

inductive CapsKind
  | snake
  | camel
  | pascal

def getCapsKind (snake : String) : CapsKind := Id.run do
  let s := snake
  let startPos := if s.startsWith "_" then ⟨1⟩ else 0
  let stopPos  := if s.endsWith "_" then s.endPos - ⟨1⟩ else s.endPos
  let s := Substring.mk s startPos stopPos
  if s.contains '_' then CapsKind.snake
  else if s.front == s.front.toLower then CapsKind.camel
  else CapsKind.pascal

def convertSnake (snake : String) : CapsKind → String
  | CapsKind.snake  => snake
  | CapsKind.camel  => snake.snake2camel
  | CapsKind.pascal => snake.snake2pascal

def cmp (x y : String) : Ordering :=
  if x < y then Ordering.lt
  else if x > y then Ordering.gt
  else Ordering.eq

end String
