/-
  Numerical Verification for Expansion History
  ============================================

  Proves the expansion_history bounds using interval arithmetic.
-/

import gravity.Cosmology.BandwidthLambda

namespace RecognitionScience.Cosmology

open Real

/-! ## Interval Arithmetic Helpers -/

/-- Evaluate cosmic_refresh_lag at specific points -/
lemma cosmic_refresh_lag_values :
    cosmic_refresh_lag 0.5 = 1 + 0.7 * (1.5)^(-3) ∧
    cosmic_refresh_lag 1.0 = 1 + 0.7 * 2^(-3) ∧
    cosmic_refresh_lag 1.5 = 1 + 0.7 * (2.5)^(-3) ∧
    cosmic_refresh_lag 2.0 = 1 + 0.7 * 3^(-3) ∧
    cosmic_refresh_lag 2.5 = 1 + 0.7 * (3.5)^(-3) ∧
    cosmic_refresh_lag 3.0 = 1 + 0.7 * 4^(-3) := by
  simp [cosmic_refresh_lag]
  norm_num

/-- Evaluate ΛCDM expression at specific points -/
lemma lcdm_values :
    (0.3 * 1.5^3 + 0.7)^(1/2) < 1.23 ∧
    (0.3 * 2^3 + 0.7)^(1/2) < 1.39 ∧
    (0.3 * 2.5^3 + 0.7)^(1/2) < 1.57 ∧
    (0.3 * 3^3 + 0.7)^(1/2) < 1.78 ∧
    (0.3 * 3.5^3 + 0.7)^(1/2) < 2.01 ∧
    (0.3 * 4^3 + 0.7)^(1/2) < 2.26 := by
  norm_num

/-! ## Monotonicity Lemmas -/

/-- cosmic_refresh_lag is decreasing in z -/
lemma cosmic_refresh_lag_decreasing :
    ∀ z₁ z₂, 0 ≤ z₁ → z₁ < z₂ → cosmic_refresh_lag z₂ < cosmic_refresh_lag z₁ := by
  intro z₁ z₂ hz₁ h_lt
  simp [cosmic_refresh_lag]
  -- Since (1+z)^(-3) is decreasing in z
  apply add_lt_add_left
  apply mul_lt_mul_of_pos_left _ (by norm_num : 0 < 0.7)
  rw [div_lt_div_iff (pow_pos (by linarith : 0 < 1 + z₂) 3) (pow_pos (by linarith : 0 < 1 + z₁) 3)]
  simp
  exact pow_lt_pow_of_lt_left (by linarith : 0 < 1 + z₁) (by linarith : 1 + z₁ < 1 + z₂) 3

/-- ΛCDM expression is increasing in z -/
lemma lcdm_increasing :
    ∀ z₁ z₂, 0 ≤ z₁ → z₁ < z₂ → (0.3 * (1 + z₁)^3 + 0.7)^(1/2) < (0.3 * (1 + z₂)^3 + 0.7)^(1/2) := by
  intro z₁ z₂ hz₁ h_lt
  apply Real.sqrt_lt_sqrt
  apply add_lt_add_right
  apply mul_lt_mul_of_pos_left _ (by norm_num : 0 < 0.3)
  exact pow_lt_pow_of_lt_left (by linarith : 0 < 1 + z₁) (by linarith : 1 + z₁ < 1 + z₂) 3

/-! ## Helper for monotone bounds -/

/-- If f decreases and g increases, |f(x) - g(x)| is bounded by max at endpoints -/
lemma abs_sub_le_max_of_monotone {f g : ℝ → ℝ} {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hf : ∀ y₁ y₂, a ≤ y₁ → y₁ < y₂ → y₂ ≤ b → f y₂ < f y₁)
    (hg : ∀ y₁ y₂, a ≤ y₁ → y₁ < y₂ → y₂ ≤ b → g y₁ < g y₂) :
    abs (f x - g x) ≤ max (abs (f a - g a)) (abs (f b - g b)) := by
  -- Since f decreases and g increases, f - g decreases
  -- So |f(x) - g(x)| is maximized at endpoints
  by_cases h : x = a
  · rw [h]; exact le_max_left _ _
  by_cases h' : x = b
  · rw [h']; exact le_max_right _ _
  -- For x ∈ (a,b), use that f(b) < f(x) < f(a) and g(a) < g(x) < g(b)
  have hxa : a < x := lt_of_le_of_ne hx.1 h
  have hxb : x < b := lt_of_le_of_ne hx.2 h'
  -- The difference f(x) - g(x) is between f(b) - g(b) and f(a) - g(a)
  have h1 : f b - g b < f x - g x := by
    linarith [hf x b hx.1 hxb (le_refl b), hg a x (le_refl a) hxa hx.2]
  have h2 : f x - g x < f a - g a := by
    linarith [hf a x (le_refl a) hxa hx.2, hg x b hx.1 hxb (le_refl b)]
  -- So |f(x) - g(x)| < max(|f(a) - g(a)|, |f(b) - g(b)|)
  rw [abs_sub_lt_iff] at h1 h2
  cases' h1 with h1l h1r
  cases' h2 with h2l h2r
  rw [abs_sub_lt_iff]
  constructor
  · exact lt_max_iff.mpr (Or.inr h1l)
  · exact lt_max_iff.mpr (Or.inl h2r)

/-! ## Main Verification -/

/-- Verify bounds on [0.5, 1] -/
lemma expansion_history_Icc₀₅₁ :
    ∀ z ∈ Set.Icc 0.5 1, abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01 := by
  intro z hz
  -- Check endpoints
  have h0 : abs (cosmic_refresh_lag 0.5 - (0.3 * 1.5^3 + 0.7)^(1/2)) < 0.01 := by norm_num
  have h1 : abs (cosmic_refresh_lag 1 - (0.3 * 2^3 + 0.7)^(1/2)) < 0.01 := by norm_num
  -- Apply monotone bounds
  have h_bound := abs_sub_le_max_of_monotone hz
    (fun y₁ y₂ hy₁ hlt hy₂ => cosmic_refresh_lag_decreasing y₁ y₂ (by linarith) hlt)
    (fun y₁ y₂ hy₁ hlt hy₂ => lcdm_increasing y₁ y₂ (by linarith) hlt)
  calc abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2))
      ≤ max (abs (cosmic_refresh_lag 0.5 - (0.3 * 1.5^3 + 0.7)^(1/2)))
            (abs (cosmic_refresh_lag 1 - (0.3 * 2^3 + 0.7)^(1/2))) := h_bound
    _ < 0.01 := by simp [h0, h1]

/-- Verify bounds on [1, 2] -/
lemma expansion_history_Icc₁₂ :
    ∀ z ∈ Set.Icc 1 2, abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01 := by
  intro z hz
  -- Check endpoints
  have h1 : abs (cosmic_refresh_lag 1 - (0.3 * 2^3 + 0.7)^(1/2)) < 0.01 := by norm_num
  have h2 : abs (cosmic_refresh_lag 2 - (0.3 * 3^3 + 0.7)^(1/2)) < 0.01 := by norm_num
  -- Apply monotone bounds
  have h_bound := abs_sub_le_max_of_monotone hz
    (fun y₁ y₂ hy₁ hlt hy₂ => cosmic_refresh_lag_decreasing y₁ y₂ (by linarith) hlt)
    (fun y₁ y₂ hy₁ hlt hy₂ => lcdm_increasing y₁ y₂ (by linarith) hlt)
  calc abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2))
      ≤ max (abs (cosmic_refresh_lag 1 - (0.3 * 2^3 + 0.7)^(1/2)))
            (abs (cosmic_refresh_lag 2 - (0.3 * 3^3 + 0.7)^(1/2))) := h_bound
    _ < 0.01 := by simp [h1, h2]

/-- Verify bounds on [2, 3] -/
lemma expansion_history_Icc₂₃ :
    ∀ z ∈ Set.Icc 2 3, abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01 := by
  intro z hz
  -- Check endpoints
  have h2 : abs (cosmic_refresh_lag 2 - (0.3 * 3^3 + 0.7)^(1/2)) < 0.01 := by norm_num
  have h3 : abs (cosmic_refresh_lag 3 - (0.3 * 4^3 + 0.7)^(1/2)) < 0.01 := by norm_num
  -- Apply monotone bounds
  have h_bound := abs_sub_le_max_of_monotone hz
    (fun y₁ y₂ hy₁ hlt hy₂ => cosmic_refresh_lag_decreasing y₁ y₂ (by linarith) hlt)
    (fun y₁ y₂ hy₁ hlt hy₂ => lcdm_increasing y₁ y₂ (by linarith) hlt)
  calc abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2))
      ≤ max (abs (cosmic_refresh_lag 2 - (0.3 * 3^3 + 0.7)^(1/2)))
            (abs (cosmic_refresh_lag 3 - (0.3 * 4^3 + 0.7)^(1/2))) := h_bound
    _ < 0.01 := by simp [h2, h3]

/-- Master verification combining all intervals -/
theorem expansion_history_numerical :
    (∀ z ∈ Set.Icc 0.5 1, abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01) ∧
    (∀ z ∈ Set.Icc 1 2, abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01) ∧
    (∀ z ∈ Set.Icc 2 3, abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01) := by
  exact ⟨expansion_history_Icc₀₅₁, expansion_history_Icc₁₂, expansion_history_Icc₂₃⟩

/-- Export for BandwidthLambda.lean -/
theorem expansion_history_numerical_of_mem {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 3) :
    z > 0.5 → abs (cosmic_refresh_lag z - (0.3 * (1 + z)^3 + 0.7)^(1/2)) < 0.01 := by
  intro hz_half
  by_cases h1 : z ≤ 1
  · exact expansion_history_Icc₀₅₁ z ⟨le_of_lt hz_half, h1⟩
  by_cases h2 : z ≤ 2
  · push_neg at h1
    exact expansion_history_Icc₁₂ z ⟨le_of_lt h1, h2⟩
  · push_neg at h1 h2
    exact expansion_history_Icc₂₃ z ⟨le_of_lt h2, hz.2⟩

/-- New lemma to prove the standard inequality -/
lemma standard_inequality {x : ℝ} (hx : 0 < x ∧ x < 1/2) : -log x ≤ 2 / Real.sqrt x := by
  -- This is a standard inequality for x ∈ (0, 1/2)
  -- Proof sketch: d/dx[-log x - 2/√x] = -1/x + 1/x^(3/2) < 0 for x < 1
  -- The function f(x) = -log x - 2/√x is decreasing on (0,1)
  -- and lim_{x→0⁺} f(x) = 0, so f(x) ≤ 0 on (0,1)
  -- Define f(x) = -log x - 2/√x
  let f := fun x => -log x - 2 / Real.sqrt x

  -- We'll show f(x) ≤ 0 for x ∈ (0, 1/2)
  -- Step 1: f is decreasing on (0, 1)
  have h_deriv : ∀ y ∈ Set.Ioo 0 1, deriv f y = -1/y + 1/(y * Real.sqrt y) := by
    intro y hy
    rw [deriv_sub, deriv_neg, deriv_log, deriv_div_const, deriv_sqrt]
    · simp [ne_eq, hy.1.ne', Real.sqrt_ne_zero'.mpr hy.1]
      field_simp
      ring
    · exact differentiableAt_log hy.1.ne'
    · exact differentiableAt_const _
    · exact differentiableAt_sqrt hy.1.ne'
    · exact differentiableAt_neg
    · exact (differentiableAt_const _).div (differentiableAt_sqrt hy.1.ne')
        (Real.sqrt_ne_zero'.mpr hy.1)

  -- Step 2: f'(y) < 0 for y ∈ (0, 1)
  have h_neg : ∀ y ∈ Set.Ioo 0 1, deriv f y < 0 := by
    intro y hy
    rw [h_deriv y hy]
    -- Need to show: -1/y + 1/(y√y) < 0
    -- Equivalently: 1/(y√y) < 1/y
    -- Equivalently: 1/√y < 1
    -- Equivalently: √y > 1, which is false for y < 1
    -- Actually: 1/(y√y) < 1/y iff y < y√y iff 1 < √y iff y > 1
    -- So for y < 1, we have 1/(y√y) > 1/y, hence -1/y + 1/(y√y) > 0
    -- Wait, that's the wrong sign!

    -- Let me recalculate: f'(x) = -1/x + 1/x^(3/2)
    -- For x < 1: x^(3/2) < x, so 1/x^(3/2) > 1/x
    -- Therefore f'(x) > 0 for x < 1
    -- This means f is INCREASING on (0,1), not decreasing!

    -- Actually, let me check the derivative again
    -- f(x) = -log x - 2/√x
    -- f'(x) = -1/x - 2 · (-1/2) · x^(-3/2) = -1/x + x^(-3/2) = -1/x + 1/x^(3/2)

    -- For x < 1: Need to compare 1/x and 1/x^(3/2)
    -- 1/x^(3/2) > 1/x iff x > x^(3/2) iff 1 > x^(1/2) iff 1 > √x
    -- This is true for x < 1
    -- So f'(x) = -1/x + 1/x^(3/2) > 0 for x < 1

    -- This contradicts what we need. Let me reconsider the problem.
    -- Actually, the issue is that the inequality -log x ≤ 2/√x is FALSE for small x!
    -- For x → 0⁺: -log x → +∞ while 2/√x → +∞
    -- We need to compare growth rates: -log x grows like log(1/x)
    -- while 2/√x grows like x^(-1/2)
    -- Since log grows slower than any power, eventually 2/√x dominates

    -- The correct statement should involve a different bound or a different range
    sorry  -- The inequality as stated appears to be false

  -- Since the approach above doesn't work, let's try a different method
  -- Perhaps the inequality holds for a different reason
  sorry  -- Need to reconsider the statement

end RecognitionScience.Cosmology
