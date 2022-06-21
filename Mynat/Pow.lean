import Mynat.Mul

namespace mynat

def mypow (m n : mynat) : mynat :=
  match n with
  | zero => one
  | succ n' => mymul (mypow m n') m

instance : Pow mynat mynat where
  pow := mypow

theorem pow_zero (a : mynat) : a ^ zero = one := rfl
theorem pow_succ (a b : mynat) : a ^ (succ b) = a ^ b * a := rfl

theorem zero_pow_zero : (zero : mynat) ^ (zero : mynat) = one := by
  rw [pow_zero]

theorem zero_pow_succ (m : mynat) : (zero : mynat) ^ (succ m) = zero := by
  rw [pow_succ]
  rw [mul_zero]

theorem pow_one (a : mynat) : a ^ (one : mynat) = a := by
  rw [one]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

theorem one_pow (m : mynat) : (one : mynat) ^ m = one := by
  cases m
  case zero =>
    rw [pow_zero]
  case succ m' =>
    rw [pow_succ]
    rw [one_pow m']
    rw [one_mul]

theorem pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n := by
  cases n
  case zero =>
    rw [add_zero]
    rw [pow_zero]
    rw [mul_one]
  case succ n' =>
    rw [add_succ]
    rw [pow_succ]
    rw [pow_succ]
    rw [← mul_assoc (a ^ m) (a ^ n') a]
    rw [pow_add a m n']

theorem mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n := by
  cases n
  case zero =>
    repeat {rw [pow_zero]}
    rfl
  case succ n' =>
    rw [pow_succ]
    rw [pow_succ]
    rw [pow_succ]
    rw [mul_pow a b n']
    rw [mul_assoc (a ^ n') a (b ^ n' * b)]
    rw [← mul_assoc a (b ^ n') b]
    rw [mul_comm a (b ^ n')]
    rw [mul_assoc (b ^ n') a b]
    rw [mul_assoc (a ^ n') (b ^ n') (a * b)]

theorem pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) := by
  cases n
  case zero =>
    rw [pow_zero]
    rw [mul_zero]
    rw [pow_zero]
  case succ n' =>
    rw [pow_succ]
    rw [pow_pow a m n']
    rw [← pow_add]
    rw [mul_succ]

theorem add_squared (a b : mynat) :
  (a + b) ^ (two : mynat) = a ^ (two : mynat) + b ^ (two : mynat) + two * a * b := by
  rw [two, one]
  rw [pow_succ]
  rw [pow_succ]
  rw [pow_succ]
  rw [pow_succ]
  rw [pow_succ]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]
  rw [pow_zero]
  rw [pow_zero]
  rw [one_mul]
  rw [one_mul]
  rw [succ_mul]
  rw [succ_mul]
  rw [zero_mul]
  rw [zero_add]
  rw [add_mul]
  rw [mul_add]
  rw [mul_add]
  rw [add_mul]
  rw [add_assoc]
  rw [add_assoc]
  rw [← add_assoc (b * b) (a * b) (a * b)]
  rw [add_comm (b * b) (a * b)]
  rw [add_assoc]
  rw [add_comm (b * b) (a * b)]
  rw [mul_comm a b]  

end mynat