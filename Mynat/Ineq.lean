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

theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) := sorry
theorem zero_le (a : mynat) : zero ≤ a := sorry
theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := sorry
theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b := sorry
theorem le_zero (a : mynat) (h : a ≤ zero) : a = zero := sorry
theorem succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b := sorry
theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a := sorry
theorem le_succ_self (a : mynat) : a ≤ succ a := sorry
theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := sorry
theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b := sorry
theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) := sorry
theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b := sorry
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