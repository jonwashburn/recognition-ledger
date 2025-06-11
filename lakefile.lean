import Lake
open Lake DSL

package «recognition-ledger» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «RecognitionScience» where
  globs := #[.submodules `formal]
