/-- Exponential sum is greater than exponential of sum -/
lemma exp_sum_gt {n : ℕ} (hn : n > 1) (p : Fin n → ℝ)
  (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
  ∑ i, Real.exp (p i) > Real.exp 1 := by
  -- Key insight: exp is strictly convex, so Jensen's inequality gives
  -- exp(∑ p_i · 1) < ∑ p_i · exp(1) when p_i are not all equal
  -- Since ∑ p_i = 1 and n > 1, not all p_i can equal 1
  -- This forces at least one p_i < 1, making the inequality strict

  -- First show that not all p_i are equal
  have h_not_all_equal : ∃ i j, p i ≠ p j := by
    by_contra h_all_eq
    push_neg at h_all_eq
    -- If all p_i are equal, then p_i = 1/n for all i
    have h_val : ∀ i, p i = 1 / n := by
      intro i
      -- Sum of n equal values equals 1
      have : (n : ℝ) * p i = ∑ j : Fin n, p i := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [h_all_eq i] at this
      rw [← this, hsum]
      field_simp
    -- But then p 0 = 1/n < 1 (since n > 1)
    have : p 0 < 1 := by
      rw [h_val 0]
      rw [div_lt_one]
      · exact Nat.one_lt_cast.mpr hn
      · exact Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
    -- And p 0 = 1/n > 0
    have h_pos : p 0 > 0 := hp 0
    -- So we have at least two distinct values in the range [0,1]
    -- Actually, we need to show they can't all be equal to make Jensen strict
    use 0, 1
    intro h_eq
    -- If p 0 = p 1, and all are equal, then all p_i = 1/n
    have : p 0 = 1 / n := h_val 0
    have : p 1 = 1 / n := h_val 1
    -- But this means n ≥ 2 distinct indices have the same value 1/n
    -- This is fine - we need a different approach
    -- The contradiction is that if all p_i = 1/n with n > 1, then no p_i = 1
    -- But we need at least one p_i ≠ 1/n to apply strict Jensen
    -- Actually, we already have what we need: all p_i = 1/n < 1
    sorry  -- This approach needs refinement

  -- Apply Jensen's inequality for strictly convex functions
  -- For strictly convex f and weights p_i with ∑p_i = 1:
  -- f(∑ p_i x_i) < ∑ p_i f(x_i) when not all x_i are equal
  -- Here x_i = 1 for all i, so we get f(1) < ∑ p_i f(1) = f(1)
  -- This is wrong - we need the reverse direction

  -- Actually, we want to show ∑ exp(p_i) > exp(∑ p_i) = exp(1)
  -- This is NOT Jensen's inequality - it's a different statement
  -- We need: ∑ exp(p_i) > n * exp(1/n) for p_i summing to 1
  -- And then show n * exp(1/n) > exp(1) for n > 1

  -- Lemma: For n > 1, we have n * exp(1/n) > exp(1)
  have h_bound : (n : ℝ) * Real.exp (1 / n) > Real.exp 1 := by
    -- Take log of both sides: log(n) + 1/n > 1
    -- Equivalently: log(n) > 1 - 1/n = (n-1)/n
    -- For n ≥ 2, this holds because log is concave
    sorry  -- Requires real analysis

  -- Now use AM-GM type inequality for exponentials
  -- The minimum of ∑ exp(p_i) subject to ∑ p_i = 1 occurs when all p_i = 1/n
  -- This gives n * exp(1/n) > exp(1)
  sorry  -- Complete using convexity of exp
