import Mynat.Ineq

namespace mynat

theorem strong_induction (P : mynat → Prop) (H : ∀ n : mynat, (∀ m : mynat, m < n → P m) → P n) (n : mynat) : P n := by
  have hpz : P zero := by
    have hz := H zero
    have : ∀ m : mynat, m < zero → P m := by
      intro m
      intro hmz
      apply False.elim
      rw [lt_def] at hmz
      have := le_zero m hmz.left
      rw [this] at hmz
      exact hmz.right (le_refl 0)
    exact hz this
  let Q n := ∀ x : mynat, x ≤ n → P x
  have hqimpp : ∀ x : mynat, Q x → P x := by
    intro x
    intro hqn
    apply hqn x
    exact le_refl x
  apply hqimpp
  induction n
  case a.zero =>
    intro z
    intro hz
    have := le_zero z hz
    rw [this]
    exact hpz
  case a.succ n' hn' =>
    have hltn' : ∀ m : mynat, m < succ n' → P m := by
      intro m
      intro hmn'
      have := hn' m
      rw [lt_iff_succ_le] at hmn'
      exact this (le_of_succ_le_succ _ _ hmn')
    have := H (succ n') hltn'
    intro x
    intro hxn'
    apply Or.elim (Classical.em (x = succ n'))
    . intro hxxn'
      rw [hxxn']
      exact this
    . intro hxxn'
      have := (lt_aux_weak x (succ n')).mp ⟨ hxn', hxxn' ⟩
      exact hltn' x this

def pred (m : mynat) : mynat :=
  match m with
  | zero => zero
  | succ m' => m'

-- Careful: a - b + b may not be equal to a !
def mysub (m n : mynat) : mynat :=
  match n with
  | zero => m
  | succ n' => mysub (pred m) n'

instance : Sub mynat where
  sub := mysub

theorem sub_eq_mysub (m n : mynat) : m - n = mysub m n := rfl

theorem pred_succ_eq_self (n : mynat) : pred (succ n) = n := by rw [pred]
theorem succ_pred_eq_self (n : mynat) : n ≠ 0 → succ (pred n) = n := by
  intro h
  cases n
  case zero =>
    apply False.elim
    exact h rfl
  case succ n' =>
    rw [pred_succ_eq_self]

theorem le_of_pred_le_pred (a b : mynat) : a ≠ 0 → b ≠ 0 → pred a ≤ pred b → a ≤ b := by
  intro hanz hbnz h
  have := succ_le_succ (pred a) (pred b) h
  rw [succ_pred_eq_self a hanz] at this
  rw [succ_pred_eq_self b hbnz] at this
  exact this

theorem le_pred (a b : mynat) : a ≤ b → pred a ≤ pred b := by
  intro h
  cases a
  case zero =>
    rw [pred]
    simp
    exact zero_le (pred b)
  case succ a' =>
    cases b
    case zero =>
      have := le_zero (succ a') h
      apply False.elim
      exact succ_ne_zero a' this
    case succ b' =>
      rw [pred_succ_eq_self, pred_succ_eq_self]
      exact le_of_succ_le_succ a' b' h

theorem add_pred (a b : mynat) : b ≠ 0 → a + pred b = pred (a + b) := by
  intro h
  cases b
  case zero =>
    apply False.elim
    exact h (Eq.refl 0)
  case succ b' =>
    rw [pred_succ_eq_self]
    rw [add_succ]
    rw [pred_succ_eq_self]

theorem pred_add (a b : mynat) : a ≠ 0 → pred a + b = pred (a + b) := by
  intro h
  cases a
  case zero =>
    apply False.elim
    exact h (Eq.refl 0)
  case succ a' =>
    rw [pred_succ_eq_self]
    rw [succ_add]
    rw [pred_succ_eq_self]

theorem sub_zero (a : mynat) : a - 0 = a := by
  rw [sub_eq_mysub]
  rfl

theorem sub_add_eq_add_sub (a b c : mynat) : b ≤ a → a - b + c = a + c - b := by
  intro h
  rw [sub_eq_mysub, sub_eq_mysub]
  induction b generalizing a
  case zero =>
    rw [mysub, mysub]
  case succ b' hb' =>
    rw [mysub, mysub]
    have hanz : a ≠ 0 := by
      cases a
      case zero =>
        have := le_zero (succ b') h
        apply False.elim _
        exact succ_ne_zero b' this
      case succ a' =>
        exact succ_ne_zero a'
    have hthis := hb' (pred a)
    rw [← pred_succ_eq_self b'] at hthis
    have := hthis (le_pred (succ b') a h)
    rw [pred_succ_eq_self] at this
    rw [this]
    rw [pred_add _ _ hanz]

theorem succ_sub_succ (m n : mynat) : succ m - succ n = m - n := by
  rw [sub_eq_mysub, sub_eq_mysub]
  rw [mysub]
  rw [pred_succ_eq_self]

theorem sub_add_eq_self (m n : mynat) : n ≤ m → m - n + n = m := by
  intro h
  rw [sub_add_eq_add_sub m n n h]
  induction n
  case zero =>
    rw [mynat_zero_eq_zero, add_zero]
    rw [sub_zero]
  case succ n' hn' =>
    have := le_trans _ _ _ (le_succ_self n') h
    have := hn' this
    rw [add_succ]
    rw [succ_sub_succ]
    exact this

theorem pred_le_self (m : mynat) : pred m ≤ m := by
  cases m
  case zero =>
    exists 0
  case succ m' =>
    rw [pred_succ_eq_self]
    exact le_succ_self m'

theorem pred_sub (m n : mynat) : pred m - n = pred (m - n) := by
  cases n
  case zero =>
    rw [mynat_zero_eq_zero, sub_zero, sub_zero]
  case succ n' =>
    rw [sub_eq_mysub, mysub]
    rw [sub_eq_mysub, mysub]
    rw [← sub_eq_mysub, ← sub_eq_mysub]
    rw [pred_sub (pred m) n']

theorem sub_succ (m n : mynat) : m - succ n = pred (m - n) := by
  rw [sub_eq_mysub, mysub]
  rw [← pred_sub]
  rw [sub_eq_mysub]

theorem sub_le_sub (m n : mynat) : m ≤ n → ∀ t : mynat, m - t ≤ n - t := by
  intro h
  intro t
  induction t
  case zero =>
    rw [mynat_zero_eq_zero]
    rw [sub_zero, sub_zero]
    exact h
  case succ t' ht' =>
    rw [sub_succ]
    rw [sub_succ]
    exact le_pred _ _ ht'

theorem sub_self_eq_zero (n : mynat) : n - n = 0 := by
  cases n
  case zero =>
    rfl
  case succ n' =>
    rw [succ_sub_succ]
    exact sub_self_eq_zero n'

theorem succ_sub (m n : mynat) : n ≤ m → succ m - n = succ (m - n) := by
  intro h
  induction n generalizing m
  case zero =>
    rw [sub_eq_mysub, mysub]
    rw [mynat_zero_eq_zero, sub_zero]
  case succ n' hn' =>
    rw [succ_sub_succ, sub_succ]
    have : 0 < m - n' := by
      rw [lt_iff_succ_le]
      have := sub_le_sub (succ n') m h n'
      have haux := hn' n' (le_refl n')
      rw [haux] at this
      rw [sub_self_eq_zero] at this
      exact this
    have := ((lt_aux_weak 0 (m - n')).mpr this).right
    exact Eq.symm (succ_pred_eq_self (m - n') (Ne.symm this))

theorem sub_pred (m n : mynat) : n ≠ 0 → n ≤ m → m - pred n = succ (m - n) := by
  intro h hnm
  cases n
  case zero =>
    apply False.elim
    exact h (Eq.refl 0)
  case succ n' =>
    rw [pred_succ_eq_self]
    rw [sub_succ]
    cases hnm with
    | intro c hc =>
      rw [hc]
      rw [succ_add, succ_sub]
      rw [pred_succ_eq_self]
      exists c

theorem add_sub_assoc (a b c : mynat) : c ≤ b → a + b - c = a + (b - c) := by
  intro h
  induction c
  case zero =>
    rw [mynat_zero_eq_zero]
    rw [sub_zero, sub_zero]
  case succ c' hc' =>
    have := le_trans _ _ _ (le_succ_self c') h
    have := hc' this
    have hdp : b - c' ≠ 0 := by
      have := sub_le_sub _ _ h c'
      rw [succ_sub _ _ (le_refl c')] at this
      rw [sub_self_eq_zero] at this
      intro hfalse
      rw [hfalse] at this
      exact not_succ_le_self 0 this
    rw [sub_succ, sub_succ, add_pred _ _ hdp]
    rw [this]

end mynat