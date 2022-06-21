import Mynat.Add

namespace mynat

-- Not sure if I'm correct by writing these lines...
-- Seems like I cannot copy directly from https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/src/mynat/definition.lean
axiom zero_ne_succ (m : mynat) : (zero : mynat) ≠ succ m
axiom succ_inj {m n : mynat} (h : succ m = succ n) : m = n

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

theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b := by
  cases t
  case zero =>
    rw [add_zero]
    rw [add_zero]
    intro H
    exact H
  case succ t' =>
    rw [add_succ]
    rw [add_succ]
    intro h
    have hh := succ_inj h
    exact (add_right_cancel a t' b) hh

theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b := by
  rw [add_comm t a]
  rw [add_comm t b]
  exact add_right_cancel a t b

theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b := by
  apply Iff.intro
  . exact add_right_cancel a t b
  . intro H
    rw [H]

theorem eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = zero := by
  intro h
  conv at h =>
    rhs
    rw [← add_zero a]
  have hcanc := add_left_cancel a b zero
  exact hcanc h

theorem succ_ne_zero (a : mynat) : succ a ≠ zero := by
  simp

theorem add_left_eq_zero {{a b : mynat}} (H : a + b = zero) : b = zero := by
  cases b
  case zero =>
    rfl
  case succ b' =>
    rw [add_succ] at H
    have h' := (succ_ne_zero (a+b')) H
    apply False.elim
    exact h'

theorem add_right_eq_zero {a b : mynat} : a + b = zero → a = zero := by
  rw [add_comm]
  intro h
  exact add_left_eq_zero h

theorem add_one_eq_succ (d : mynat) : d + one = succ d := by
  rw [succ_eq_add_one]

theorem ne_succ_self (n : mynat) : n ≠ succ n := by
  intro H
  rw [← add_one_eq_succ n] at H
  conv at H =>
    lhs
    rw [← add_zero n]
  have hfalse := add_left_cancel n zero one H
  rw [one] at hfalse
  exact zero_ne_succ zero hfalse

end mynat