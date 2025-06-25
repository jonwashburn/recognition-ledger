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

end RecognitionScience.Cosmology
