-- Insert lean 3 code here.
import other

namespace foo

/-- test -/
@[simp] def foo := other

theorem foo_eq_one : foo.foo = 1 := rfl

end foo
