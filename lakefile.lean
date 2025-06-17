import Lake
open Lake DSL

package «recognition-ledger» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

@[default_target]
lean_lib «RecognitionScience» where
  srcDir := "formal"
