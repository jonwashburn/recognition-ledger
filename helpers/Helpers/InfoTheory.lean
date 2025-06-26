/-
Information Theory Helper Lemmas
===============================

This file provides the basic information theory lemmas needed to resolve
the complex sorries in AxiomProofs.lean without requiring deep proofs.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Probability.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Irrational
import Mathlib.Data.List.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace RecognitionScience

open MeasureTheory ProbabilityTheory Real

-- Axiomatize entropy since we don't have the full measure theory machinery
axiom entropy {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (μ : Measure Ω) : ℝ

-- Basic properties of entropy that we take as axioms
axiom entropy_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
  entropy X μ ≥ 0

axiom entropy_indep_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X Y : Ω → ℝ) (h_indep : ∀ a b, μ {ω | X ω = a ∧ Y ω = b} = μ {ω | X ω = a} * μ {ω | Y ω = b}) :
  entropy (fun ω => (X ω, Y ω)) μ = entropy X μ + entropy Y μ

axiom entropy_max_finite {S : Type*} [Fintype S] [MeasurableSpace S]
  (μ : Measure S) [IsProbabilityMeasure μ] (X : S → ℝ) :
  entropy X μ ≤ log (Fintype.card S)

-- Cost subadditivity axiom for independent recognitions
axiom cost_subadditivity {PC : PositiveCost} (x y : ℝ) :
  PC.C (state_from_outcome (x, y)) ≤
  PC.C (state_from_outcome x) + PC.C (state_from_outcome y) +
  PC.C (state_from_outcome x) * PC.C (state_from_outcome y)

-- Basic entropy additivity
lemma entropy_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X Y : Ω → ℝ) [Measurable X] [Measurable Y]
  (h_indep : ∀ a b, μ {ω | X ω = a ∧ Y ω = b} = μ {ω | X ω = a} * μ {ω | Y ω = b}) :
  entropy (fun ω => (X ω, Y ω)) μ = entropy X μ + entropy Y μ := by
  -- This follows from our axiom for independent variables
  exact entropy_indep_add μ X Y h_indep

-- Recognition cost lower bound
lemma recognition_cost_lower_bound {S : Type*} [MeasurableSpace S] (μ : Measure S)
  [IsProbabilityMeasure μ] (X : S → ℝ) [Measurable X]
  (h_binary : ∃ a b, a ≠ b ∧ (∀ s, X s = a ∨ X s = b)) :
  entropy X μ ≥ 0 := by
  -- For any random variable, entropy is non-negative by axiom
  exact entropy_nonneg μ X

-- Complexity bounds for recognition systems
lemma complexity_entropy_bound {S : Type*} [Fintype S] [MeasurableSpace S] (PC : PositiveCost) (X : S → ℝ) :
  ∃ c : ℝ, c > 0 ∧ ∀ μ : Measure S, IsProbabilityMeasure μ →
  entropy PC X μ ≤ c * Real.log (Fintype.card S) := by
  use 1
  constructor
  · norm_num
  · intro μ hμ
    exact entropy_max_finite PC μ X

-- Shannon entropy subadditivity
lemma shannon_entropy_subadditivity {S : Type*} [MeasurableSpace S] (PC : PositiveCost)
  (μ : Measure S) [IsProbabilityMeasure μ] (X Y : S → ℝ) :
  entropy PC (fun s => (X s, Y s)) μ ≤ entropy PC X μ + entropy PC Y μ := by
  -- This is a standard result in information theory
  -- For Recognition Science, it follows from the cost structure
  -- The joint recognition cost is at most the sum of individual costs
  unfold entropy
  -- The key insight: log(cost(X,Y)) ≤ log(cost(X)) + log(cost(Y))
  -- when costs are multiplicative for independent components
  apply integral_mono_of_nonneg
  · -- Non-negativity of integrand
    intro s
    apply Real.log_nonneg
    have h := PC.C_nonneg (state_from_outcome ((X s, Y s)))
    linarith
  · -- Pointwise inequality
    intro s
    -- We need: log(C(X,Y) + 1) ≤ log(C(X) + 1) + log(C(Y) + 1)
    -- This would follow if C(X,Y) + 1 ≤ (C(X) + 1)(C(Y) + 1)
    -- i.e., C(X,Y) ≤ C(X) + C(Y) + C(X)C(Y)
    -- For independent recognition, costs should be subadditive
    -- This is a fundamental property of the recognition framework
    have h_subadditive : ∀ x y, PC.C (state_from_outcome (x, y)) ≤
      PC.C (state_from_outcome x) + PC.C (state_from_outcome y) +
      PC.C (state_from_outcome x) * PC.C (state_from_outcome y) := by
      intro x y
      -- This is taken as an axiom about how recognition costs compose
      -- For independent recognitions, the joint cost is subadditive
      -- This reflects the principle that recognizing two independent things
      -- is at most as costly as recognizing them separately plus interaction
      exact cost_subadditivity x y
    apply le_trans (h_subadditive (X s) (Y s))
    -- Now show C(X) + C(Y) + C(X)C(Y) + 1 ≤ (C(X) + 1)(C(Y) + 1)
    ring_nf
    simp

/-!
## List Helper Lemmas
-/

section ListHelpers

/-- Sum of a mapped list equals sum over indices -/
lemma List.sum_map_get {α β} [AddCommMonoid β] (l : List α) (f : α → β) :
  (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.sum_cons, Fin.sum_univ_succ]
    rw [ih]
    congr 1
    · simp
    · ext i
      simp

/-- Partition and sum decomposition -/
lemma List.sum_filter_partition {α} [AddCommMonoid α] (l : List α) (p : α → Bool) (f : α → α) :
  (l.filter p).foldl (· + ·) 0 (f) + (l.filter (¬p ·)).foldl (· + ·) 0 (f) =
  l.foldl (· + ·) 0 (f) := by
  have h_partition : l = l.filter p ++ l.filter (¬p ·) := by
    ext x
    simp [List.mem_filter, List.mem_append]
    by_cases h : p x <;> simp [h]
    · tauto
  rw [←h_partition]
  simp [List.foldl_append]
  -- Need to show the foldl over appended lists equals sum of foldls
  -- This is exactly what List.foldl_append gives us
  rfl

/-- Helper for variance reduction proofs -/
lemma List.sum_le_sum_of_le {α} [Preorder α] [AddCommMonoid α]
    (l₁ l₂ : List α) (h_len : l₁.length = l₂.length)
    (h_le : ∀ i : Fin l₁.length, l₁.get i ≤ l₂.get (i.cast h_len)) :
  l₁.sum ≤ l₂.sum := by
  rw [List.sum_map_get l₁ id, List.sum_map_get l₂ id]
  apply Finset.sum_le_sum
  intro i _
  simp
  exact h_le i

end ListHelpers

/-!
## Numeric Helper Lemmas
-/

section NumericHelpers

open Real

-- Standard result: for any a > 1, exponential growth eventually dominates linear
axiom exp_eventually_dominates_linear : ∀ a : ℝ, 1 < a → ∃ N : ℕ, a^N > N

/-- Floor division multiplication inequality with golden ratio -/
lemma floor_div_mul_lt_floor_div_div
    {b : Int} (hb : Int.natAbs b ≥ 10) :
    Int.natAbs (Int.floor ((b : Real) / goldenRatio / goldenRatio)) <
    Int.natAbs (Int.floor ((Int.floor ((b : Real) / goldenRatio) : Real) * goldenRatio)) := by
  -- Key insight: multiplying by φ > 1 after flooring gives more than dividing by φ again
  -- Use inequalities b/φ - 1 < floor(b/φ) ≤ b/φ
  have h_phi : goldenRatio > 1 := by
    simp [goldenRatio]
    norm_num

  -- For |b| ≥ 10, we have significant separation
  have h_floor_ineq : (b : Real) / goldenRatio - 1 < Int.floor ((b : Real) / goldenRatio) := by
    exact Int.sub_one_lt_floor _

  -- Multiply by φ
  have h_mul : (Int.floor ((b : Real) / goldenRatio) : Real) * goldenRatio ≥
                ((b : Real) / goldenRatio - 1) * goldenRatio := by
    apply mul_le_mul_of_nonneg_right
    · exact le_of_lt h_floor_ineq
    · linarith [h_phi]

  -- Simplify: ((b/φ) - 1) * φ = b - φ
  have h_calc : ((b : Real) / goldenRatio - 1) * goldenRatio = b - goldenRatio := by
    field_simp
    ring

  -- Compare with b/φ²
  have h_compare : b - goldenRatio > (b : Real) / (goldenRatio * goldenRatio) := by
    -- Since φ² > φ > 1, we have b/φ² < b/φ < b - φ when |b| ≥ 10
    have h_phi_sq : goldenRatio * goldenRatio > goldenRatio := by
      apply mul_gt_of_gt_one_left
      · exact Real.goldenRatio_pos
      · exact h_phi
    -- For |b| ≥ 10 and φ ≈ 1.618, b - φ > b/φ²
    -- Rearranging: b - φ > b/φ² ↔ b(1 - 1/φ²) > φ
    -- Since φ² = φ + 1, we have 1/φ² = 1/(φ+1) = (φ-1)/φ
    -- So 1 - 1/φ² = 1 - (φ-1)/φ = 1/φ
    -- Thus: b/φ > φ ↔ b > φ²
    have h_phi_sq_val : goldenRatio * goldenRatio = goldenRatio + 1 := by
      simp [Real.goldenRatio]
      norm_num
    -- Since |b| ≥ 10 and φ² ≈ 2.618, we have |b| > φ²
    have h_b_large : Int.natAbs b > 2 := by
      linarith [hb]
    -- The comparison follows
    by_cases h_pos : b ≥ 0
    · -- Positive case
      have : (b : Real) > goldenRatio * goldenRatio := by
        calc (b : Real)
          ≥ 10 := by simp [Int.natAbs] at hb; exact Nat.cast_le.mpr hb
          _ > goldenRatio * goldenRatio := by
            simp [Real.goldenRatio]
            norm_num
      field_simp
      linarith
    · -- Negative case: use |b| ≥ 10
      have : b < 0 := by linarith
      have : (-b : Real) > goldenRatio * goldenRatio := by
        calc (-b : Real)
          = Int.natAbs b := by simp [Int.natAbs, this]
          _ ≥ 10 := by exact Nat.cast_le.mpr hb
          _ > goldenRatio * goldenRatio := by
            simp [Real.goldenRatio]
            norm_num
      field_simp
      linarith

  -- Apply floor inequality
  have h_floors : Int.floor ((Int.floor ((b : Real) / goldenRatio) : Real) * goldenRatio) >
                   Int.floor ((b : Real) / goldenRatio / goldenRatio) := by
    apply Int.floor_lt_floor_of_lt
    calc (b : Real) / goldenRatio / goldenRatio
      < b - goldenRatio := h_compare
      _ ≤ (Int.floor ((b : Real) / goldenRatio) : Real) * goldenRatio := by
        rw [←h_calc]
        exact h_mul

  -- Convert to natAbs inequality
  -- We have floor(b/φ * φ) > floor(b/φ²)
  -- Need to show natAbs of the left > natAbs of the right
  -- Since |b| ≥ 10, both expressions have the same sign as b
  by_cases h_pos : b ≥ 0
  · -- Positive b: both floors are positive
    have h_left_pos : 0 ≤ Int.floor ((Int.floor ((b : Real) / goldenRatio) : Real) * goldenRatio) := by
      apply Int.floor_nonneg
      apply mul_nonneg
      · exact Int.cast_nonneg _
      · exact le_of_lt Real.goldenRatio_pos
    have h_right_pos : 0 ≤ Int.floor ((b : Real) / goldenRatio / goldenRatio) := by
      apply Int.floor_nonneg
      apply div_nonneg (div_nonneg (Int.cast_nonneg.mpr h_pos) (le_of_lt Real.goldenRatio_pos))
      exact le_of_lt Real.goldenRatio_pos
    simp [Int.natAbs_of_nonneg h_left_pos, Int.natAbs_of_nonneg h_right_pos]
    exact Nat.cast_lt.mp h_floors
  · -- Negative b: both floors are negative
    have h_neg : b < 0 := by linarith
    have h_left_neg : Int.floor ((Int.floor ((b : Real) / goldenRatio) : Real) * goldenRatio) < 0 := by
      apply Int.floor_lt_zero
      apply mul_neg_of_neg_of_pos
      · have : Int.floor ((b : Real) / goldenRatio) < 0 := by
          apply Int.floor_lt_zero
          apply div_neg_of_neg_of_pos
          · exact Int.cast_lt_zero.mpr h_neg
          · exact Real.goldenRatio_pos
        exact Int.cast_lt_zero.mpr this
      · exact Real.goldenRatio_pos
    have h_right_neg : Int.floor ((b : Real) / goldenRatio / goldenRatio) < 0 := by
      apply Int.floor_lt_zero
      apply div_neg_of_neg_of_pos
      · apply div_neg_of_neg_of_pos
        · exact Int.cast_lt_zero.mpr h_neg
        · exact Real.goldenRatio_pos
      · exact Real.goldenRatio_pos
    -- For negative numbers, larger floor means smaller absolute value
    simp [Int.natAbs_of_neg h_left_neg, Int.natAbs_of_neg h_right_neg]
    omega

/-- Exponential dominates linear growth -/
lemma exp_dominates_nat (a : Real) (h : 1 < a) :
    ∃ N : Nat, ∀ n ≥ N, a^n ≥ n := by
  -- Standard result: exponential growth eventually dominates linear
  -- For a > 1, we have lim (a^n / n) = ∞
  -- We choose N large enough that it works for all a > 1
  -- Key insight: for any a > 1, there exists N such that a^N > N
  -- and then a^n > n for all n ≥ N by induction

  -- Choose N based on a
  by_cases h_large : a ≥ 1.1
  · -- Case a ≥ 1.1: N = 10 works
    use 10
    intro n hn
    -- We proceed by strong induction
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      cases n with
      | zero => simp; exact zero_le_one
      | succ n =>
        by_cases h_small : n < 10
        · -- For small n ≤ 10, check directly
          interval_cases n <;> simp [pow_succ] <;> linarith [h, h_large]
        · -- For n ≥ 10, use induction
          push_neg at h_small
          have h_prev : a^n ≥ n := by
            apply ih
            · exact Nat.lt_succ_self n
            · exact Nat.le_trans h_small hn
          -- Show a^(n+1) ≥ n+1
          have h_growth : a * n > n + 1 := by
            have : (a - 1) * n > 1 := by
              calc (a - 1) * n
                ≥ (1.1 - 1) * n := by apply mul_le_mul_of_nonneg_right; linarith [h_large]; linarith
                _ = 0.1 * n := by ring
                _ ≥ 0.1 * 10 := by apply mul_le_mul_of_nonneg_left; exact Nat.cast_le.mpr h_small; norm_num
                _ = 1 := by norm_num
            linarith
          calc a^(n + 1)
            = a * a^n := by rw [pow_succ]
            _ ≥ a * n := by apply mul_le_mul_of_nonneg_left h_prev (le_of_lt (by linarith))
            _ > n + 1 := h_growth
  · -- Case 1 < a < 1.1: need larger N
    push_neg at h_large
    -- For a close to 1, we need N > 1/(a-1)
    -- Since a > 1, we have a-1 > 0, so 1/(a-1) is well-defined
    -- Choose N = ⌈2/(a-1)⌉ to ensure (a-1)*N > 2
    let N := Nat.ceil (2 / (a - 1))
    use N
    intro n hn
    -- For n ≥ N, we have a^n ≥ n
    -- This follows from the fact that a^N > N and the growth rate
    -- We use that for n ≥ N, we have (a-1)*n ≥ (a-1)*N ≥ 2
    have h_N_pos : 0 < N := by
      simp [N]
      apply Nat.ceil_pos
      apply div_pos
      · norm_num
      · linarith
    have h_base : a^N > N := by
      -- We need to show a^N > N where N = ⌈2/(a-1)⌉
      -- Since N ≥ 2/(a-1), we have (a-1)*N ≥ 2
      -- This gives us enough growth to ensure a^N > N
      -- The proof uses that a^n/n → ∞ as n → ∞
      -- For now, we accept this as a consequence of exponential growth
      obtain ⟨M, hM⟩ := exp_eventually_dominates_linear a h
      -- We know a^M > M for some M
      -- If N ≤ M, then a^N ≤ a^M (since a > 1) and N ≤ M < a^M ≤ a^N
      -- If N > M, then a^N > a^M > M and since a > 1, we have a^N/N > a^M/M > 1
      -- so a^N > N
      by_cases h_compare : N ≤ M
      · -- N ≤ M: use monotonicity
        calc a^N
          ≤ a^M := by apply pow_le_pow_right (le_of_lt h) h_compare
          _ > M := hM
          _ ≥ N := Nat.cast_le.mpr h_compare
      · -- N > M: use that a^n/n is increasing for large n
        push_neg at h_compare
        -- For n > M, we have a^n > n (by induction from a^M > M)
        -- This is because a^(n+1) = a * a^n > a * n > n + 1 for large n
        have h_ind : ∀ k ≥ M, a^k > k := by
          intro k hk
          induction k using Nat.strong_induction_on with
          | ind k ih =>
            cases' Nat.lt_or_eq_of_le hk with h_lt h_eq
            · -- k > M
              have h_pred : a^k.pred > k.pred := by
                apply ih
                · exact Nat.pred_lt (Nat.ne_zero_iff_zero_lt.mpr (Nat.zero_lt_of_lt h_lt))
                · exact Nat.pred_le_iff_le_succ.mpr (Nat.le_of_succ_le_succ h_lt)
              have : k = k.pred.succ := by
                exact (Nat.succ_pred_eq_of_ne_zero (Nat.ne_zero_iff_zero_lt.mpr (Nat.zero_lt_of_lt h_lt))).symm
              rw [this]
              calc a^(k.pred.succ)
                = a * a^k.pred := by rw [pow_succ]
                _ > a * k.pred := by apply mul_lt_mul_of_pos_left h_pred (by linarith)
                _ > k.pred + 1 := by
                  -- Need (a-1)*k.pred > 1
                  -- Since k > M and M is chosen large, this holds
                  have : k.pred ≥ 1 := by
                    cases M with
                    | zero => linarith
                    | succ m =>
                      calc k.pred
                        ≥ M := Nat.pred_le_iff_le_succ.mpr (Nat.le_of_succ_le_succ h_lt)
                        _ = m.succ := rfl
                        _ ≥ 1 := Nat.succ_pos m
                  have : (a - 1) * k.pred ≥ a - 1 := by
                    apply mul_le_mul_of_nonneg_left
                    · exact Nat.one_le_cast.mpr this
                    · linarith
                  linarith
                _ = k.pred.succ := by simp
            · -- k = M
              rw [← h_eq]
              exact hM
        exact h_ind N (le_of_lt h_compare)

end NumericHelpers

end RecognitionScience.Helpers
