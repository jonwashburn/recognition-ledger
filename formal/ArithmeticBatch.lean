import Mathlib.Data.Real.Basic

namespace ArithmeticBatch

-- Basic arithmetic theorems that should work with norm_num
theorem two_plus_two : (2 : ℝ) + 2 = 4 := by norm_num

theorem three_plus_five : (3 : ℝ) + 5 = 8 := by norm_num

theorem four_times_three : (4 : ℝ) * 3 = 12 := by norm_num

theorem ten_minus_six : (10 : ℝ) - 6 = 4 := by norm_num

theorem eight_div_two : (8 : ℝ) / 2 = 4 := by norm_num

-- Basic inequalities
theorem five_gt_three : (5 : ℝ) > 3 := by norm_num

theorem seven_ge_seven : (7 : ℝ) ≥ 7 := by norm_num

theorem nine_lt_ten : (9 : ℝ) < 10 := by norm_num

theorem six_le_eight : (6 : ℝ) ≤ 8 := by norm_num

-- Positivity
theorem one_pos : (1 : ℝ) > 0 := by norm_num

theorem two_pos : (2 : ℝ) > 0 := by norm_num

theorem pi_approx_pos : (3.14159 : ℝ) > 0 := by norm_num

-- Powers
theorem two_squared : (2 : ℝ)^2 = 4 := by norm_num

theorem three_cubed : (3 : ℝ)^3 = 27 := by norm_num

-- Fractions
theorem half_plus_half : (1/2 : ℝ) + 1/2 = 1 := by norm_num

theorem quarter_times_four : (1/4 : ℝ) * 4 = 1 := by norm_num

-- More complex but still numerical
theorem lcm_two_four : Nat.lcm 2 4 = 4 := by norm_num

theorem lcm_three_six : Nat.lcm 3 6 = 6 := by norm_num

theorem gcd_twelve_eight : Nat.gcd 12 8 = 4 := by norm_num

end ArithmeticBatch
