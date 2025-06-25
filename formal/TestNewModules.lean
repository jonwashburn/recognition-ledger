/-
Test file to verify new module structure
-/

-- Test Journal imports
import foundation.RecognitionScience.Journal.API
import foundation.RecognitionScience.Journal.Predictions
import foundation.RecognitionScience.Journal.Verification

-- Test Philosophy imports
import foundation.RecognitionScience.Philosophy.Ethics
import foundation.RecognitionScience.Philosophy.Death
import foundation.RecognitionScience.Philosophy.Purpose

-- Test Numerics imports
import foundation.RecognitionScience.Numerics.PhiComputation
import foundation.RecognitionScience.Numerics.ErrorBounds

namespace RecognitionScience.Test

open Journal Philosophy Numerics

-- Test that we can access definitions from each module
#check API.submitAxiom
#check Predictions.allPredictions
#check Verification.experimentalDatabase

#check Ethics.golden_rule
#check Death.information_conservation
#check Purpose.fundamental_purpose

#check PhiComputation.phi_power_approx
#check ErrorBounds.electron_mass_within_bounds

-- Success message
def modules_load_successfully : String :=
  "All new Recognition Science modules load correctly!"

#eval IO.println modules_load_successfully

end RecognitionScience.Test
