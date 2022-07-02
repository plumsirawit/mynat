import Myint.Mul

namespace myint

theorem ne_irrefl (a : myint) : ¬ a ≉ a := by
  rw [mynotequal]
  rw [Ne]
  have := refl a
  rw [myequal] at this
  rw [this]
  have : ¬ a.y + a.x = a.y + a.x → False := by
    intro h
    rw [← Ne] at h
    exact Ne.irrefl h
  exact this

theorem ne_symm {a b : myint} (hab : mynotequal a b) : mynotequal b a := by
  rw [mynotequal] at hab ⊢
  have hres := Ne.symm hab
  rw [mynat.add_comm a.y, mynat.add_comm a.x] at hres
  exact hres

-- Warning: this is not the usual transitivity.
-- this says that if a ≠ b and b = c then a ≠ c
theorem ne_trans {a b c : myint} (hab : mynotequal a b) (hbc : myequal b c) : mynotequal a c := by
  rw [myequal] at hbc
  rw [mynotequal] at hab ⊢
  have : a.x + b.y + (b.x + c.y) ≠ a.y + b.x + (b.y + c.x) := by
    rw [hbc]
    intro h
    have := mynat.add_right_cancel (a.x + b.y) (b.y + c.x) (a.y + b.x) h
    exact hab this
  repeat rw [← mynat.add_assoc] at this
  rw [mynat.add_assoc a.x] at this
  rw [mynat.add_comm b.y] at this
  rw [mynat.add_comm a.x] at this
  rw [mynat.add_assoc a.y] at this
  rw [mynat.add_comm a.y] at this
  repeat rw [mynat.add_assoc (b.x + b.y)] at this
  intro hfalse
  rw [hfalse] at this
  exact this (Eq.refl (b.x + b.y + (a.y + c.x)))


theorem ne_implies_exists_offset (a b : myint) : a ≉ b → ∃ c : myint, c ≉ 0 ∧ a ≈ b + c := by
  intro h
  rw [mynotequal] at h
  cases mynat.le_total (a.x + b.y) (a.y + b.x)
  case inl hle =>
    rw [mynat.le_iff_exists_add] at hle
    cases hle with
    | intro d hd =>
      exists myint.mk 0 d
      apply And.intro
      . rw [mynotequal]
        rw [destruct_x, destruct_y _ d]
        rw [default_nat_has_no_y, default_nat_has_same_x]
        rw [mynat.myofnat, mynat.mynat_zero_eq_zero]
        repeat rw [mynat.add_zero]
        cases d
        case zero =>
          apply False.elim _
          rw [mynat.mynat_zero_eq_zero, mynat.add_zero] at hd
          exact h (Eq.symm hd)
        case succ d' =>
          exact Ne.symm (mynat.succ_ne_zero d')
      . rw [equiv_is_myequal, myequal]
        rw [add_y, destruct_y _ d]
        rw [add_x, destruct_x 0 _]
        rw [mynat.add_zero]
        rw [← mynat.add_assoc]
        exact Eq.symm hd
  case inr hle =>
    rw [mynat.le_iff_exists_add] at hle
    cases hle with
    | intro d hd =>
      exists myint.mk d 0
      apply And.intro
      . rw [mynotequal]
        rw [destruct_x, destruct_y _ 0]
        rw [default_nat_has_no_y, default_nat_has_same_x]
        rw [mynat.myofnat, mynat.mynat_zero_eq_zero]
        repeat rw [mynat.zero_add]
        cases d
        case zero =>
          apply False.elim _
          rw [mynat.mynat_zero_eq_zero, mynat.add_zero] at hd
          exact h hd
        case succ d' =>
          rw [mynat.add_zero]
          exact mynat.succ_ne_zero d'
      . rw [equiv_is_myequal, myequal]
        rw [add_y, destruct_y _ 0]
        rw [add_x, destruct_x d _]
        rw [mynat.add_zero]
        rw [← mynat.add_assoc]
        exact hd

theorem ne_iff_exists_offset (a b : myint) : a ≉ b ↔ ∃ c : myint, c ≉ 0 ∧ a ≈ b + c := by
  apply Iff.intro
  . exact ne_implies_exists_offset a b
  . intro h
    cases h with
    | intro d hd =>
      have hdnz := hd.left
      have hab := hd.right
      rw [mynotequal]
      rw [equiv_is_myequal, myequal] at hab
      rw [add_y, add_x] at hab
      rw [mynotequal, zerox, zeroy, mynat.add_zero, mynat.add_zero] at hdnz
      intro hcont
      repeat rw [← mynat.add_assoc] at hab
      rw [hcont] at hab
      have := (mynat.add_left_cancel _ _ _) hab
      exact hdnz (Eq.symm this)

theorem ne_mul_still_ne (a b t : myint) : a ≉ b ∧ t ≉ 0 → a * t ≉ b * t := by
  intro h
  have hab := h.left
  have htnz := h.right
  have hoffset := (ne_iff_exists_offset a b).mp hab
  cases hoffset with
  | intro c hc =>
    have hcnz := hc.left
    have habc := hc.right
    have htimes := mul_right a (b + c) t habc
    have : a * t ≈ b * t + c * t := trans htimes (add_mul b c t)
    intro hfalse
    rw [← myequal, ← equiv_is_myequal] at hfalse
    have := trans (symm hfalse) this
    have := add_left_cancel (b * t) 0 (c * t) this
    have := eq_zero_or_eq_zero_of_mul_eq_zero c t (symm this)
    cases this
    case inl h' =>
      exact hcnz h'
    case inr h' =>
      exact htnz h'

theorem mul_nonzero (a b : myint) : a ≉ 0 → b ≉ 0 → a * b ≉ 0 := by
  intro ha
  intro hb
  have := ne_mul_still_ne a 0 b ⟨ ha, hb ⟩
  have := ne_trans this (zero_mul b)
  exact this

end myint