import Mynat.Ineq
import Myint.Add

namespace myint

def myneg (m : myint) : myint :=
  myint.mk m.y m.x

instance : Neg myint where
  neg := myneg

theorem neg_eq_myneg (m : myint) : -m = myneg m := rfl

def mysub (m n : myint) : myint :=
  m + myneg n

instance : Sub myint where
  sub := mysub

theorem sub_eq_mysub (m n : myint) : m - n = mysub m n := rfl
theorem sub_eq_plusneg (m n : myint) : m - n = m + (-n) := rfl

-- This proves that -m is an additive inverse of m and an identity is 0.
theorem neg_is_inv (m : myint) : m + (-m) ≈ 0 := by
  rw [neg_eq_myneg]
  rw [equiv_is_myequal]
  rw [myneg]
  rw [myequal]
  rw [add_x, add_y]
  rw [destruct_x m.y m.x]
  rw [destruct_y m.y m.x]
  rw [mynat.add_comm m.x m.y]
  rw [zerox, zeroy]

theorem negneg_eq_self (m : myint) : -(-m) ≈ m := by
  rw [neg_eq_myneg]
  rw [neg_eq_myneg]
  rw [equiv_is_myequal]
  rw [myneg]
  rw [myneg]
  rw [destruct_y]
  rw [destruct_x m.y m.x]
  rw [myequal]
  rw [destruct_x]
  rw [destruct_y]
  rw [mynat.add_comm]

example : (5 : myint) - (2 : myint) ≈ (3 : myint) := by
  have : (3 : myint) ≈ (3 : myint) := rfl
  have : (3 : myint) ≈ (3 : myint) + (0 : myint) := by exact add_zero 3
  have : (3 : myint) ≈ (3 : myint) + (2 - 2 : myint) := by
    rw [sub_eq_plusneg]
    have htinv := symm (neg_is_inv 2)
    rw [← equiv_is_myequal] at htinv
    have hleft := add_left 3 0 (2 + -2) htinv
    have happ := trans this hleft
    rw [← equiv_is_myequal] at happ
    exact happ
  rw [sub_eq_plusneg] at this
  have htrans := _root_.trans this (symm (add_assoc (3 : myint) (2 : myint) (-2 : myint)))
  rw [← equiv_is_myequal] at htrans
  have : (3 : myint) + (2 : myint) ≈ (5 : myint) := by
    apply if_x_and_y_equal_then_equiv
    rw [add_x]
    rw [add_y]
    apply And.intro
    case a.left =>
      rw [OfNat.ofNat, instOfNatMyint, myintofnat]
      simp
      rw [myofnat, myofnat, myofnat, myofnat]
      rw [OfNat.ofNat, instOfNatMyint, myintofnat]
      simp
      rw [myofnat, myofnat, myofnat]
      rw [mynat.add_succ, mynat.add_succ, mynat.succ_add, mynat.succ_add]
      rw [mynat_zero_eq_zero, mynat.zero_add]
      conv =>
        rhs
        rw [OfNat.ofNat, instOfNatMyint, myintofnat]
        simp
    case a.right =>
      rw [OfNat.ofNat, instOfNatMyint, myintofnat]
      simp
      rw [mynat.zero_add]
      rw [OfNat.ofNat, instOfNatMyint, myintofnat]
      simp
      conv =>
        rhs
        rw [OfNat.ofNat, instOfNatMyint, myintofnat]
        simp
  have hr := (add_right _ _ (-2)) this
  have htrans2 := trans htrans hr
  have hlast := symm htrans2
  rw [equiv_is_myequal]
  rw [sub_eq_plusneg]
  exact hlast

end myint