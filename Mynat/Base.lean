inductive mynat where
  | zero : mynat
  | succ : mynat → mynat
  deriving Repr

def one := mynat.succ mynat.zero
def two := mynat.succ one

namespace mynat

def myadd (m n : mynat) : mynat :=
  match n with
  | zero   => m
  | succ n' => succ (myadd m n')

instance : Add mynat where
  add := myadd

theorem add_zero (m : mynat) : m + zero = m := rfl
theorem add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

def mymul (m n : mynat) : mynat :=
  match n with
  | zero => zero
  | succ n' => myadd (mymul m n') m

instance : Mul mynat where
  mul := mymul

theorem mul_zero (a : mynat) : a * zero = zero := rfl
theorem mul_succ (a b : mynat) : a * (succ b) = a * b + a := rfl

def mypow (m n : mynat) : mynat :=
  match n with
  | zero => one
  | succ n' => mymul (mypow m n') m

instance : Pow mynat mynat where
  pow := mypow

theorem pow_zero (a : mynat) : a ^ zero = one := rfl
theorem pow_succ (a b : mynat) : a ^ (succ b) = a ^ b * a := rfl

end mynat