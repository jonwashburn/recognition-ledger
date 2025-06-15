import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- The golden ratio φ = (1 + √5) / 2 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- Test: φ is positive -/
theorem phi_pos : φ > 0 := by
  unfold φ
  norm_num
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)

/-- Test: φ > 1 -/
theorem phi_gt_one : φ > 1 := by
  unfold φ
  rw [div_gt_iff]
  · norm_num
    exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  · norm_num

/-- Test: φ satisfies the golden ratio equation -/
theorem phi_equation : φ^2 = φ + 1 := by
  unfold φ
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  ring
