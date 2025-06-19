import Lake
open Lake DSL

package «RecognitionScience» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «RecognitionScience» where
  globs := #[.submodules `formal]

@[default_target]
lean_exe «recognition-science» where
  root := `Main
