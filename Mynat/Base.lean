inductive mynat where
  | zero : mynat
  | succ : mynat → mynat
  deriving Repr

def myofnat (n : Nat) :=
  match n with
  | 0 => mynat.zero
  | Nat.succ n' => mynat.succ (myofnat n')

instance : OfNat mynat n where
  ofNat := myofnat n

def tonat (n : mynat) :=
  match n with
  | mynat.zero => 0
  | mynat.succ n' => Nat.succ (tonat n')

instance : Coe mynat Nat where
  coe := tonat

theorem mynat_zero_eq_zero : mynat.zero = 0 := rfl
theorem one_eq_succ_zero : 1 = mynat.succ 0 := rfl

