import Lake
open Lake DSL

package «RecognitionScience» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Expose the zero-axiom foundation as internal libs
lean_lib «foundation» where
  srcDir := "foundation"

-- Formal proofs and applications
lean_lib «formal» where
  srcDir := "formal"

-- Physics applications
lean_lib «physics» where
  srcDir := "physics"

-- Ethics applications
lean_lib «ethics» where
  srcDir := "ethics"

-- Ledger implementations
lean_lib «ledger» where
  srcDir := "ledger"

-- Navier-Stokes working directory
lean_lib «NavierStokes» where
  srcDir := "working/NavierStokes/Src"

@[default_target]
lean_lib «RecognitionScience» where
  roots := #[`RecognitionScience]
