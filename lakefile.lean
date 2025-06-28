import Lake
open Lake DSL

package «RecognitionScience» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Expose the zero-axiom foundation as internal libs
lean_lib «foundation» where
  globs := #[.submodules `foundation]

-- Formal proofs and applications
lean_lib «formal» where
  globs := #[.submodules `formal]

-- Physics applications
lean_lib «physics» where
  globs := #[.submodules `physics]

-- Pattern layer
lean_lib «pattern» where
  globs := #[.submodules `pattern]

-- Ethics applications
lean_lib «ethics» where
  globs := #[.submodules `ethics]

-- Ledger implementations
lean_lib «ledger» where
  globs := #[.submodules `ledger]

-- Navier-Stokes working directory
lean_lib «NavierStokes» where
  srcDir := "working/NavierStokes/Src"

@[default_target]
lean_lib «RecognitionScience» where
  roots := #[`RecognitionScience]
