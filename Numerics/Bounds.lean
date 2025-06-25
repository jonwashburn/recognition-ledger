/-
Numerics.Bounds
===============

Tiny collection of helper lemmas used for quick numerical
inequality and absolute-value proofs throughout the project.
We avoid heavy tactics: most results follow from `linarith` and
`norm_num` once the goal is reduced to elementary arithmetic.
-/

import Mathlib.Tactic

open Real

namespace RecognitionScience.Numerics

/--
If a real value `x` is known to lie between two bounds `a≤x≤b` and a target
value `t` is also between the same two bounds, then `|x − t|` is smaller than
the half-width of the interval.  This is often enough for the error goals we
use ("within 0.005", etc.).
-/
lemma abs_diff_lt_of_bounds {a b x t ε : ℝ}
    (hε : 0 < ε)
    (h_width : b - a ≤ ε)
    (h_a_le_x : a ≤ x) (h_x_le_b : x ≤ b)
    (h_a_le_t : a ≤ t) (h_t_le_b : t ≤ b) :
    |x - t| < ε := by
  have h1 : |x - t| ≤ b - a := by
    have : - (b - a) ≤ x - t ∧ x - t ≤ b - a := by
      have hxt1 : x - t ≥ a - b := by linarith
      have hxt2 : x - t ≤ b - a := by linarith
      exact ⟨hxt1, hxt2⟩
    simpa [abs_le] using this
  have : (b - a) < ε := by
    linarith
  exact lt_of_le_of_lt h1 this

/-- Convenience wrapper when the interval is specified by its midpoint `c`
    and half-width `δ`. -/
lemma abs_diff_lt_of_center {x t c δ ε : ℝ}
    (hδ : 0 < δ) (hε : δ ≤ ε)
    (hx : |x - c| ≤ δ) (ht : |t - c| ≤ δ) :
    |x - t| < ε := by
  have h_bounds_x : c - δ ≤ x ∧ x ≤ c + δ := by
    have := abs_le.1 hx; simpa using this
  have h_bounds_t : c - δ ≤ t ∧ t ≤ c + δ := by
    have := abs_le.1 ht; simpa using this
  exact abs_diff_lt_of_bounds (by positivity) (by linarith)
    h_bounds_x.1 h_bounds_x.2 h_bounds_t.1 h_bounds_t.2

end RecognitionScience.Numerics
