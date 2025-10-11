import Lake
open Lake DSL

package «YangMillsMassGap» where
  -- add package configuration options here

lean_lib «YangMills» where
  -- add library configuration options here

@[default_target]
lean_exe «yangmillsmassgap» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

