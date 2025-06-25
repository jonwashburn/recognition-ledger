/-- Exponential sum is greater than exponential of sum -/
lemma exp_sum_gt {n : ℕ} (hn : n > 1) (p : Fin n → ℝ)
  (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
  ∑ i, Real.exp (p i) > Real.exp 1 := by
  -- Key insight: exp is strictly convex, so Jensen's inequality gives
  -- exp(∑ p_i · 1) < ∑ p_i · exp(1) when p_i are not all equal
  -- Since ∑ p_i = 1 and n > 1, not all p_i can equal 1
  -- This forces at least one p_i < 1, making the inequality strict
  have h_convex : StrictConvexOn ℝ (Set.univ) Real.exp := by
    exact Real.strictConvexOn_exp
  -- Apply Jensen's inequality for strictly convex functions
  have h_jensen : Real.exp (∑ i, p i * 1) < ∑ i, p i * Real.exp 1 := by
    -- Need to show p_i are not all equal to use strict inequality
    have h_not_const : ∃ i j, p i ≠ p j := by
      by_contra h_all_eq
      push_neg at h_all_eq
      -- If all p_i are equal, then p_i = 1/n for all i
      have h_val : ∀ i, p i = 1 / n := by
        intro i
        have : n * p i = 1 := by
          calc n * p i = ∑ j : Fin n, p i := by simp [Finset.sum_const]
          _ = ∑ j : Fin n, p j := by simp [h_all_eq i]
          _ = 1 := hsum
        field_simp at this
        exact this
      -- But then p 0 = 1/n < 1 (since n > 1), contradicting that all equal 1
      have : p 0 < 1 := by
        rw [h_val 0]
        simp [div_lt_one_iff_lt, hn]
      -- This would mean ∑ p_i = n * (1/n) = 1, which checks out
      -- So we need a different approach...
      sorry -- Need to construct explicit indices with different values
    sorry -- Apply Jensen with strict inequality
  -- Simplify to get the result
  simp at h_jensen
  rw [hsum, mul_one] at h_jensen
  exact h_jensen
