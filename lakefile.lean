import Lake
open Lake DSL

package leansieve {}

lean_lib PrimeGen { }
lean_lib PrimeSieve { }
lean_lib ASeq { }
lean_lib Rake { }
lean_lib RakeMap { }
lean_lib RakeSieve { }
lean_lib Results { }

@[default_target]
lean_exe leansieve {
  root := `Main}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
