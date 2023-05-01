import Lake
open Lake DSL

package joyOfAbstraction {
  -- add package configuration options here
}

require mathlib from
    "/Users/monade/git/mathlib" with NameMap.empty

lean_lib JoyOfAbstraction {
  -- add library configuration options here
}

-- @[defaultTarget]
lean_exe joyOfAbstraction {
  root := `Main
}
