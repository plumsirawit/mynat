import Myint.Base

namespace myint

def myadd (m n : myint) : myint :=
  myint.mk (m.x + n.x) (m.y + n.y)

instance : Add myint where
  add := myadd

theorem add_zero (m : myint) : m + 0 = m := rfl

theorem zero_add (n : myint) : { x := 0, y := 0} + n = n := by
  cases n
  case mk x y =>
    sorry
    

theorem add_assoc (a b c : myint) : (a + b) + c = a + (b + c) := by
  sorry

theorem add_comm (a b : myint) : a + b = b + a := by
  sorry

theorem add_right_comm (a b c : myint) : a + b + c = a + c + b := by
  sorry

attribute [simp] add_assoc add_comm add_right_comm

end myint