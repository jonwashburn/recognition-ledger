import Lake
open Lake DSL

package NavierStokesLedger {
  -- Project configuration
  srcDir := "Src"
}

-- Main library with public interface
lean_lib NavierStokesLedger {
  -- Only export the public theorems
  roots := #[`NavierStokesLedger.Theorems, `NavierStokesLedger.Constants]
}

-- Mathlib dependency
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
