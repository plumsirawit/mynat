import Mynat.Ineq

structure myint where
  x : mynat
  y : mynat

def myequal (a b : myint) : Prop :=
  (a.x + b.y) = (a.y + b.x)

def myintofnat (n : Nat) :=
  myint.mk (myofnat n) 0

instance : OfNat myint n where
  ofNat := myintofnat n

def toInt (n : myint) :=
  (n.x : Int) - (n.y : Int)

instance : Coe myint Int where
  coe := toInt
