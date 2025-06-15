import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- The golden ratio φ = (1 + √5) / 2 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- The cost functional J(x) = (x + 1/x) / 2 -/
noncomputable def J (x : ℝ) : ℝ := (x + 1/x) / 2

namespace SimpleGoldenRatio

/-- φ is positive -/
theorem phi_pos : φ > 0 := by
  unfold φ
  positivity

/-- φ > 1 -/
theorem phi_gt_one : φ > 1 := by
  unfold φ
  norm_num

/-- Simple arithmetic test -/
theorem two_plus_three : (2 : ℝ) + 3 = 5 := by norm_num

/-- Another simple test -/
theorem five_times_two : (5 : ℝ) * 2 = 10 := by norm_num

end SimpleGoldenRatio
