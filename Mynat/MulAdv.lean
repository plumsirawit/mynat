import Mynat.AddAdv
import Mynat.Mul

namespace mynat

theorem mul_pos (a b : mynat) : a ≠ zero → b ≠ zero → a * b ≠ zero := sorry
theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = zero) :
  a = zero ∨ b = zero := sorry
theorem mul_eq_zero_iff (a b : mynat): a * b = zero ↔ a = zero ∨ b = zero := sorry
theorem mul_left_cancel (a b c : mynat) (ha : a ≠ zero) : a * b = a * c → b = c := sorry

end mynat