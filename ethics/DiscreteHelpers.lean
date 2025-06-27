/-
  Recognition Science - Ethics: Discrete Helpers

  Helper lemmas for handling discrete approximations in moral dynamics.
  The discrete nature of ledger operations creates technical challenges.
-/

import Ethics.Curvature
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic

namespace RecognitionScience.Ethics

open Int Real

/-! ## Floor operation bounds -/

/-- Floor operations can lose at most 1 per operation -/
lemma floor_loss_bound (x : ℝ) : x - 1 < ↑⌊x⌋ ∧ ↑⌊x⌋ ≤ x := by
  constructor
  · exact sub_one_lt_floor x
  · exact floor_le x

/-- Sum of floors is within n of sum of reals -/
lemma sum_floor_approximation (l : List ℝ) :
  (l.map floor).sum ≥ l.sum - l.length ∧
  (l.map floor).sum ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.sum_cons, List.map_cons]
    constructor
    · calc (floor x + (xs.map floor).sum : ℝ)
        ≥ (x - 1) + (xs.sum - xs.length) := by
          apply add_le_add
          · exact le_of_lt (sub_one_lt_floor x)
          · exact ih.1
        _ = x + xs.sum - (1 + xs.length) := by ring
        _ = (x :: xs).sum - (x :: xs).length := by simp [List.sum_cons, List.length_cons]
    · calc (floor x + (xs.map floor).sum : ℝ)
        ≤ x + xs.sum := by
          apply add_le_add
          · exact floor_le x
          · exact ih.2

/-- Mean preservation approximation for discrete operations -/
lemma discrete_mean_approximation (l : List ℝ) (h : l ≠ []) :
  let discrete_mean := (l.map floor).sum / l.length
  let continuous_mean := l.sum / l.length
  |discrete_mean - continuous_mean| ≤ 1 := by
  simp only
  have h_len : 0 < l.length := List.length_pos.mpr h
  have h_len_real : 0 < (l.length : ℝ) := Nat.cast_pos.mpr h_len

  -- Use sum_floor_approximation
  have ⟨h_lower, h_upper⟩ := sum_floor_approximation l

  -- Bound the difference
  rw [abs_sub_le_iff]
  constructor
  · -- Lower bound
    rw [sub_le_iff_le_add]
    calc (l.map floor).sum / l.length
      ≥ (l.sum - l.length) / l.length := by
        apply div_le_div_of_le_left _ h_len_real h_len_real
        exact h_lower
      _ = l.sum / l.length - 1 := by
        rw [sub_div, div_self (ne_of_gt h_len_real)]
  · -- Upper bound
    rw [sub_le_iff_le_add]
    calc continuous_mean
      = l.sum / l.length := rfl
      _ ≥ (l.map floor).sum / l.length := by
        apply div_le_div_of_le_left _ h_len_real h_len_real
        exact h_upper
      _ = discrete_mean - 0 := by simp
      _ ≤ discrete_mean + 1 := by linarith

/-! ## Variance reduction with discrete operations -/

/-- Discrete variance can increase slightly due to floor operations -/
lemma discrete_variance_bound (l : List ℝ) (mean : ℝ) :
  let discrete_l := l.map (fun x => floor (x - mean))
  let variance := l.map (fun x => (x - mean)^2) |>.sum / l.length
  let discrete_variance := discrete_l.map (fun x => (x : ℝ)^2) |>.sum / l.length
  discrete_variance ≤ variance + l.length := by
  sorry -- Technical: bound the variance increase from discretization

/-- Sufficient condition for discrete variance reduction -/
lemma discrete_variance_reduction_sufficient (l : List ℝ) (factor : ℝ)
  (h_factor : 0 < factor ∧ factor < 0.5) :
  let mean := l.sum / l.length
  let transformed := l.map (fun x => floor (x + factor * (mean - x)))
  let orig_var := l.map (fun x => (x - mean)^2) |>.sum
  let new_var := transformed.map (fun x => ((x : ℝ) - mean)^2) |>.sum
  l.length > 10 → new_var < orig_var := by
  sorry -- Prove that for reasonable list sizes, variance still reduces

/-! ## Convexity approximations -/

/-- Sum of absolute values is approximately convex under discretization -/
lemma discrete_abs_sum_convexity (l : List ℤ) (mean : ℤ)
  (h_small_mean : natAbs mean ≤ 5) :
  let centered := l.map (· - mean)
  let spread := l.map (fun x => x - mean + if x > mean then 1 else -1)
  (centered.map natAbs).sum ≤ (spread.map natAbs).sum + l.length := by
  sorry -- Show that spreading increases sum of absolute values

end RecognitionScience.Ethics
