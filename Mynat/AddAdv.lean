import Mynat.Base
import Mynat.Add

namespace mynat

theorem succ_inj' {a b : mynat} (hs : (succ a) = (succ b)) : a = b := by
  apply succ_inj
  exact hs

theorem succ_succ_inj {a b : mynat} (h : succ (succ a) = succ (succ b)) : a = b := by
  apply succ_inj
  apply succ_inj
  exact h

theorem succ_eq_succ_of_eq {a b : mynat} : a = b → (succ a) = (succ b) := by
  intro h
  rw [h]

theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b := by
  apply Iff.intro
  . exact succ_inj'
  . exact succ_eq_succ_of_eq

theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b := sorry
theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b := sorry
theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b := sorry
theorem eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = zero := sorry
theorem succ_ne_zero (a : mynat) : succ a ≠ zero := sorry
theorem add_left_eq_zero {{a b : mynat}} (H : a + b = zero) : b = zero := sorry
theorem add_right_eq_zero {a b : mynat} : a + b = zero → a = zero := sorry
theorem add_one_eq_succ (d : mynat) : d + one = succ d := sorry
theorem ne_succ_self (n : mynat) : n ≠ succ n := sorry

end mynat