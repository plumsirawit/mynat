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

lean_exe mynat {
  root := `Main
}
