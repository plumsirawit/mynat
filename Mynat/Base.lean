inductive mynat where
  | zero : mynat
  | succ : mynat → mynat
  deriving Repr

def one := mynat.succ mynat.zero
def two := mynat.succ one