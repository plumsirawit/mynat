import Myint.Ineq

namespace elemnumnat

set_option pp.explicit true

def abs (n : myint) :=
  if n.x ≤ n.y then
    n
  else
    -n

-- Division algorithm
theorem division_algorithm (a b : myint) : b ≠ 0 → ∃ q : myint, ∃ r : myint, 0 ≤ r ≤ (abs b) - 1
end elemnumnat