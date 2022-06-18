import Mynat.Base
import Mynat.Add

namespace mynat

theorem zero_mul (m : mynat) : zero * m = zero := by
  cases m
  case zero =>
    rfl
  case succ m' =>
    rw [mul_succ]
    rw [zero_mul m']
    rfl

theorem mul_one (m : mynat) : m * one = m := by
  rw [one]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]

theorem one_mul (m : mynat) : one * m = m := by
  cases m
  case zero =>
    rw [mul_zero]
  case succ m' =>
    rw [mul_succ]
    rw [one_mul m']
    rw [succ_eq_add_one]

theorem mul_add (t a b : mynat) : t * (a + b) = t * a + t * b := by
  cases b
  case zero =>
    rw [add_zero]
    rw [mul_zero]
    rw [add_zero]
  case succ b' =>
    rw [add_succ]
    rw [mul_succ]
    rw [mul_succ]
    rw [mul_add t a b']
    rw [add_assoc]

theorem mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) := by
  cases c
  case zero =>
    rw [mul_zero]
    rw [mul_zero]
    rw [mul_zero]
  case succ c' =>
    rw [mul_succ]
    rw [mul_succ]
    rw [mul_assoc a b c', mul_add]

theorem succ_mul (a b : mynat) : succ a * b = a * b + b := by
  cases b
  case zero =>
    rw [mul_zero]
    rw [mul_zero]
    rfl
  case succ b' =>
    rw [mul_succ]
    rw [mul_succ]
    rw [succ_mul a b']
    rw [add_succ]
    rw [add_succ]
    rw [add_assoc]
    rw [add_comm b' a]
    rw [add_assoc]

theorem add_mul (a b t : mynat) : (a + b) * t = a * t + b * t := by
  cases t
  case zero =>
    repeat {rw [mul_zero]}
    rfl
  case succ t' =>
    rw [mul_succ]
    rw [mul_succ]
    rw [mul_succ]
    rw [add_mul a b t']
    rw [← add_assoc]
    rw [← add_assoc]
    rw [add_assoc (a * t') (b * t') a]
    rw [add_comm (b * t') a]
    rw [add_assoc (a * t') a (b * t')]

theorem mul_comm (a b : mynat) : a * b = b * a := by
  cases b
  case zero =>
    rw [mul_zero]
    rw [zero_mul]
  case succ b' =>
    rw [mul_succ]
    rw [succ_mul]
    rw [mul_comm a b']

theorem mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [mul_comm a b]

attribute [simp] mul_assoc mul_comm mul_left_comm

end mynat