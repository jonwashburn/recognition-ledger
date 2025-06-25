import Lake
open Lake DSL

package RecognitionScience

@[default_target]
lean_lib RecognitionScience where
  srcDir := "formal"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
