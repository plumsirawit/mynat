import Myint.Ineq

namespace elemnumnat

-- Division algorithm
theorem division_algorithm (a b : myint) :
  0 < b → ∃ q : myint, ∃ r : myint, 0 ≤ r ∧ r < b ∧ a ≈ b * q + r := by
  intro hb
  cases myint.le_total 0 a
  case inl hapos =>
    cases myint.trichotomy a b
    case inl hab =>
      -- 1. a < b
      exists 0
      exists a
      apply And.intro
      . exact hapos
      . apply And.intro
        . exact hab
        . have := myint.add_right _ _ a (myint.symm (myint.mul_zero b))
          exact myint.trans (myint.symm (myint.zero_add a)) this
    case inr htmpab =>
      cases htmpab
      case inl hab =>
        -- 2. a = b
        exists 1
        exists 0
        apply And.intro
        . exact myint.le_refl 0
        . apply And.intro
          . exact hb
          . have := myint.trans (myint.symm (myint.mul_one b)) (myint.symm (myint.add_zero (b * 1)))
            exact myint.trans hab this
      case inr hab =>
        -- 3. a > b
        have := myint.canon_pos a ((myint.pos_iff_y_le_x a).mp hapos)
        cases this with
        | intro cn hcn =>
          cases cn
          case mk cnx cny =>
            rw [myint.destruct_y] at hcn
            rw [hcn.left] at hcn
            simp at hcn
            induction cnx
            sorry
  case inr haneg =>
    sorry


end elemnumnat