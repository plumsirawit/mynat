import Mynat.Base

namespace mynat

theorem zero_add (n : mynat) : zero + n = n := by
  cases n
  case zero => rfl
  case succ m =>
    have h := congrArg succ (zero_add m)
    rw [←add_succ] at h
    exact h

theorem add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) := by
  cases c
  case zero =>
    repeat {rw [add_zero]}
    rfl
  case succ m =>
    rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [add_assoc a b m]

theorem succ_add (a b : mynat) : succ a + b = succ (a + b) := by
  cases b
  case zero =>
    repeat {rw [add_zero]}
    rfl
  case succ m =>
    rw [add_succ]
    rw [add_succ]
    rw [succ_add a m]

theorem add_comm (a b : mynat) : a + b = b + a := by
  cases b
  case zero =>
    rw [add_zero]
    rw [zero_add]
  case succ m =>
    rw [add_succ]
    rw [succ_add]
    rw [add_comm a m]

theorem succ_eq_add_one (n : mynat) : succ n = n + one := by
  rw [one]
  rw [add_succ n zero]
  rw [add_zero]

theorem add_right_comm (a b c : mynat) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_assoc]
  rw [add_comm b c]

attribute [simp] add_assoc add_comm add_right_comm

end mynat