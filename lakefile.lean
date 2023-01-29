import Lake
open Lake DSL

package uniq {
  -- add package configuration options here
}

lean_lib Uniq {
  -- add library configuration options here
}

@[default_target]
lean_exe uniq {
  root := `Main
}
