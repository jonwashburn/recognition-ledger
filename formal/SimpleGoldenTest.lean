import Mathlib.Data.Real.Basic

/-- Simple test: 2 > 1 -/
theorem two_gt_one : (2 : ℝ) > 1 := by norm_num

/-- Simple test: 3 > 2 -/
theorem three_gt_two : (3 : ℝ) > 2 := by norm_num

/-- Simple test: 1.618 > 1 -/
theorem phi_approx_gt_one : (1.618 : ℝ) > 1 := by norm_num
