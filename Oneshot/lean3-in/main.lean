-- meta def m := `[skip]

structure finsupp2 (α : Type*) :=
(to_fun : α → nat)
(support : list α)
(mem_support_to_fun : ∀ a, a ∈ support ↔ to_fun a ≠ 0)

inductive hello_world : Type
| mk : nat → hello_world

def a : _ := @finsupp2.mem_support_to_fun

def blah : Type := Prop

namespace blah

def two_words (x : blah) : ℕ := 1

theorem two_words_eq (x : blah) : two_words x = 1 := rfl

end blah

namespace foo

open blah

-- /-- test -/
@[simp] def foo := 1

theorem foo_eq_one : foo.foo = 1 := rfl

theorem moo (x : blah) : x.two_words = 1 := rfl

theorem moo2 (x : blah) : two_words x = 1 := by rw [two_words_eq]

theorem moo3 (x : blah) : two_words x = 1 := by rw [x.two_words_eq]

theorem moo4 (x : blah) : two_words x = 1 := by refine x.two_words_eq

theorem moo5 (x : blah) : two_words x = 1 := by apply x.two_words_eq

theorem moo6 (x : blah) : two_words x = 1 := by refine two_words_eq _

theorem moo7 (x : blah) : two_words x = 1 := by apply two_words_eq

theorem moo8 (x : blah) : two_words x = 1 := x.two_words_eq

theorem moo9 (x : blah) : two_words x = 1 := two_words_eq _

end foo
