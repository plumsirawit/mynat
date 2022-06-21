import Mynat.AddAdv
import Mynat.MulAdv

namespace mynat

theorem one_add_le_self (x : mynat) : x ≤ one + x := by
  rw [le_iff_exists_add]
  exists one
  rw [add_comm]

theorem le_refl (x : mynat) : x ≤ x :=
  Exists.intro zero rfl

-- attribute [rfl] mynat.le_refl
-- Why doesn't it work?

theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) := by
  intro h
  cases h with
  | intro c hc =>
    exists succ c
    rw [add_succ]
    rw [hc]

theorem zero_le (a : mynat) : zero ≤ a := by
  rw [le_iff_exists_add]
  exists a
  rw [zero_add]

theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_exists_add] at hab hbc
  cases hab with
  | intro d hd =>
    cases hbc with
    | intro e he =>
      rw [hd] at he
      exists d + e
      rw [← add_assoc]
      exact he

theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | intro c hc =>
    cases hba with
    | intro d hd =>
      rw [hc] at hd
      conv at hd =>
        lhs
        rw [← add_zero a]
      rw [add_assoc] at hd
      have halc := (add_left_cancel a zero (c+d)) hd
      have halcsym := Eq.symm halc
      have hcez := add_right_eq_zero halcsym
      rw [hcez] at hc
      rw [add_zero] at hc
      exact Eq.symm hc

theorem le_zero (a : mynat) (h : a ≤ zero) : a = zero := by
  have hh := zero_le a
  exact le_antisymm a zero h hh

theorem succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b := by
  cases h with
  | intro c hc =>
    exists c
    rw [hc]
    rw [succ_add]

theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a := by
  cases b
  case zero =>
    apply Or.intro_right
    exact zero_le a
  case succ b' =>
    have hind := le_total a b'
    cases hind
    case inl h =>
      apply Or.intro_left
      cases h with
      | intro c hc =>
        exists succ c
        rw [add_succ]
        rw [hc]
    case inr h =>
      cases h with
      | intro c hc =>
        cases c
        case zero =>
          apply Or.intro_left
          exists one
          rw [hc]
          rw [add_assoc]
          rw [zero_add]
          exact succ_eq_add_one b'
        case succ c' =>
          apply Or.intro_right
          exists c'
          rw [hc]
          rw [succ_add]
          rw [add_succ]

theorem le_succ_self (a : mynat) : a ≤ succ a := by
  exists one

theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h
  cases h with
  | intro c hc =>
    intro t
    exists c
    rw [hc]
    rw [add_assoc]
    rw [add_assoc]
    rw [add_comm c t]

theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b := by
  intro h
  cases h with
  | intro c hc =>
    exists c
    rw [succ_eq_add_one] at hc
    rw [succ_eq_add_one] at hc
    rw [add_comm b one] at hc
    rw [add_comm a one] at hc
    rw [add_assoc] at hc
    exact add_left_cancel one b (a + c) hc

theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) := by
  intro h
  cases h with
  | intro c hc =>
    rw [succ_eq_add_one] at hc
    conv at hc =>
      lhs
      rw [← add_zero a]
    rw [add_assoc] at hc
    have hd := add_left_cancel a zero (one + c) hc
    rw [add_comm] at hd
    rw [← succ_eq_add_one] at hd
    have hnd := zero_ne_succ c
    exact hnd hd

theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b := by
  cases h with
  | intro c hc =>
    exists c
    rw [hc]
    rw [← add_assoc]

theorem lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := sorry
theorem lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := sorry

def mylt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a)
-- incantation so that we can use `<` notation: 
instance : LT mynat := ⟨mylt⟩
theorem lt_def (a b : mynat) : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := Iff.rfl

theorem lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b := by
  rw [lt_def]
  apply Iff.intro
  . apply lt_aux_one
  . apply lt_aux_two

end mynat