import Lake
open Lake DSL

package mynat {
  -- add package configuration options here
  srcDir :=  "."
}

@[defaultTarget]

lean_lib Mynat {
  -- add library configuration options here
}
lean_lib base
lean_lib add
lean_lib mul
lean_lib pow
lean_lib add_adv {
  libName := "AddAdv"
}
lean_lib mul_adv {
  libName := "MulAdv"
}
lean_lib ineq

lean_exe mynat {
  root := `Main
}
