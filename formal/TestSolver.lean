/-
Test file for the solver - simple theorems that should be easy to prove
-/

import RecognitionScience

namespace TestSolver

open RecognitionScience

/-- Test: 2 + 2 = 4 -/
theorem two_plus_two : 2 + 2 = 4 := by
  rfl

/-- Test: 5 > 3 -/
theorem five_gt_three : 5 > 3 := by
  norm_num

/-- Test: E_coh is positive -/
theorem E_coh_pos : E_coh > 0 := by
  unfold E_coh
  norm_num

end TestSolver
