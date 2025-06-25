/-- Exponential sum is greater than exponential of sum -/
lemma exp_sum_gt {n : ℕ} (hn : n > 1) (p : Fin n → ℝ)
  (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
  ∑ i, Real.exp (p i) > Real.exp 1 := by
  -- Key insight: exp is strictly convex, so we use a different approach
  -- We'll show that the minimum of ∑ exp(p_i) subject to ∑ p_i = 1 occurs at p_i = 1/n
  -- and then show n * exp(1/n) > exp(1) for n ≥ 2

  -- First, we need that not all p_i can equal 1 (since n > 1 and they sum to 1)
  have h_exists_small : ∃ i, p i < 1 := by
    by_contra h_all_ge
    push_neg at h_all_ge
    -- If all p_i ≥ 1, then ∑ p_i ≥ n > 1, contradiction
    have : 1 < ∑ i : Fin n, p i := by
      calc 1 < n := by exact_mod_cast hn
      _ = ∑ i : Fin n, 1 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ i : Fin n, p i := Finset.sum_le_sum (fun i _ => h_all_ge i)
    linarith

  -- The minimum value occurs when all p_i = 1/n
  -- We'll show ∑ exp(p_i) ≥ n * exp(1/n) with equality iff all p_i = 1/n
  -- Since not all p_i = 1, they can't all equal 1/n, so we get strict inequality

  -- First show n * exp(1/n) > exp(1) for n ≥ 2
  have h_bound : (n : ℝ) * Real.exp (1 / n) > Real.exp 1 := by
    -- Take log: we need log(n) + 1/n > 1
    -- Equivalently: log(n) > 1 - 1/n = (n-1)/n
    have h_log : Real.log n > 1 - 1 / n := by
      -- This is the standard inequality log(x) > 1 - 1/x for x > 1
      have : 1 < (n : ℝ) := by exact_mod_cast hn
      exact one_sub_inv_lt_log this
    -- Now exponentiate both sides
    have h_exp : Real.exp (Real.log n + 1 / n) > Real.exp 1 := by
      apply Real.exp_lt_exp.mp
      linarith
    -- Simplify LHS
    rw [Real.exp_add, Real.exp_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))] at h_exp
    exact h_exp

  -- Now we use convexity of exp to show ∑ exp(p_i) ≥ n * exp(1/n)
  -- with strict inequality when not all p_i are equal
  have h_convex : ∑ i, Real.exp (p i) ≥ (n : ℝ) * Real.exp (1 / n) := by
    -- By convexity of exp and Jensen's inequality
    -- The minimum of ∑ exp(p_i) subject to ∑ p_i = 1, p_i > 0 is achieved at p_i = 1/n
    -- This gives the value n * exp(1/n)
    -- We use the fact that exp is convex, so the average exp(p_i) ≥ exp(average p_i)
    have h_avg : (∑ i, Real.exp (p i)) / n ≥ Real.exp ((∑ i, p i) / n) := by
      -- This is Jensen's inequality for convex functions
      -- But we need the arithmetic mean version
      -- For now, we use that exp is convex
      sorry -- Technical: Jensen's inequality in arithmetic mean form
    -- Rewrite using hsum
    rw [hsum] at h_avg
    simp at h_avg
    -- Multiply both sides by n
    linarith

  -- Actually, we need strict inequality. Since not all p_i are equal to 1/n,
  -- the convexity is strict
  have h_strict : ∑ i, Real.exp (p i) > (n : ℝ) * Real.exp (1 / n) := by
    -- If all p_i = 1/n, then ∑ p_i = n * (1/n) = 1 ✓
    -- and ∑ exp(p_i) = n * exp(1/n)
    -- Since exp is strictly convex and not all p_i are equal,
    -- we get strict inequality
    by_contra h_eq
    -- If equality holds, then all p_i must equal 1/n
    have h_all_eq : ∀ i, p i = 1 / n := by
      -- This follows from strict convexity of exp
      -- Equality in Jensen iff all values are equal
      sorry -- Technical: characterization of equality case
    -- But then all p_i < 1 (since n > 1), contradicting h_exists_small
    obtain ⟨j, hj⟩ := h_exists_small
    rw [h_all_eq j] at hj
    have : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))]
      exact Nat.one_lt_cast.mpr hn
    -- Good, this is consistent. We need a different approach...
    -- Actually, the issue is that we need to show not all p_i = 1/n
    -- We know ∃ i, p i < 1, but that's consistent with all p_i = 1/n
    -- The real issue: if ∑ exp(p_i) = n * exp(1/n), then all p_i = 1/n
    -- But we haven't proven that characterization
    sorry -- Need better approach

  -- Combine the inequalities
  calc ∑ i, Real.exp (p i)
    ≥ (n : ℝ) * Real.exp (1 / n) := h_convex
    _ > Real.exp 1 := h_bound
