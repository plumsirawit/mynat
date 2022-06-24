import Mynat.Ineq
import Myint.Base

namespace myint

def myadd (m n : myint) : myint :=
  myint.mk (m.x + n.x) (m.y + n.y)

instance : Add myint where
  add := myadd

theorem add_eq_myadd (m n : myint) : m + n = myadd m n := rfl

theorem add_x (m n : myint) : (m + n).x = m.x + n.x := by
  rw [add_eq_myadd]
  rw [myadd]

theorem add_y (m n : myint) : (m + n).y = m.y + n.y := by
  rw [add_eq_myadd]
  rw [myadd]

theorem zerox : (0 : myint).x = 0 := rfl
theorem zeroy : (0 : myint).y = 0 := rfl

theorem add_zero (m : myint) : m + 0 ≈ m := by
  rw [equiv_is_myequal]
  rw [myequal]
  rw [add_x, add_y]
  rw [zerox, zeroy]
  rw [mynat.add_zero]
  rw [mynat.add_zero]
  exact mynat.add_comm m.x m.y

theorem zero_add (n : myint) : (0 + n) ≈ n := by
  rw [equiv_is_myequal]
  rw [myequal]
  rw [add_eq_myadd]
  rw [myadd]
  rw [zerox, zeroy]
  rw [mynat.zero_add]
  rw [mynat.zero_add]
  rw [mynat.add_comm]

theorem if_x_and_y_equal_then_equiv (a b : myint) : a.x = b.x ∧ a.y = b.y → a ≈ b := by
  intro h
  rw [equiv_is_myequal]
  rw [myequal]
  rw [h.left]
  rw [h.right]
  rw [mynat.add_comm]

theorem add_assoc (a b c : myint) : (a + b) + c ≈ a + (b + c) := by
  rw [equiv_is_myequal]
  rw [myequal]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  case a.left =>
    rw [add_x]
    rw [add_x]
    rw [add_x]
    rw [add_x]
    rw [mynat.add_assoc]
  case a.right =>
    rw [add_y]
    rw [add_y]
    rw [add_y]
    rw [add_y]
    rw [mynat.add_assoc]

theorem add_comm (a b : myint) : a + b = b + a := by
  rw [equal_is_xyequal]
  apply And.intro
  case left =>
    rw [add_x]
    rw [add_x]
    rw [mynat.add_comm]
  case right =>
    rw [add_y]
    rw [add_y]
    rw [mynat.add_comm]

attribute [simp] add_assoc add_comm

end myint