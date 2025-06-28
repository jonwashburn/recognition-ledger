/-
  Recognition Science: Foundation Main
  ===================================

  Main entry point for the foundation module.
  Re-exports all foundation components.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

-- Import the main foundation module
import RecognitionScience

-- Import parameter constants
-- Note: Constants.lean has circular dependency with derivations
-- import Parameters.Constants
import Parameters.RealConstants

namespace foundation

-- Re-export key definitions
export RecognitionScience
-- export Parameters.Constants -- Circular dependency
export RecognitionScience.Constants (φ E_coh τ₀ lambda_rec c h_bar k_B T_CMB T_room)

end foundation
