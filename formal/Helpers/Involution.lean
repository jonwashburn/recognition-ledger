/-
Two-Fixed-Point Involution
==========================

A clean construction of an involution J : ℝ → ℝ with exactly two fixed points.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace RecognitionScience.Helpers

open Real

/-- The flip-around-midpoint involution that fixes a and b -/
def flipInvolution {a b : ℝ} (hab : a < b) : ℝ → ℝ := fun x =>
  if x = a ∨ x = b then x else a + b - x

variable {a b : ℝ} (hab : a < b)

/-- The function is involutive -/
theorem flipInvolution_involutive :
  Function.Involutive (flipInvolution hab) := by
  intro x
  unfold flipInvolution
  by_cases h : x = a ∨ x = b
  · -- Fixed points case
    simp [h]
  · -- Non-fixed points case
    push_neg at h
    simp [h]
    -- Need to show: if y = a + b - x and y ≠ a ∧ y ≠ b, then a + b - y = x
    have hy_ne : a + b - x ≠ a ∧ a + b - x ≠ b := by
      constructor
      · intro heq
        have : x = b := by linarith
        exact h.2 this
      · intro heq
        have : x = a := by linarith
        exact h.1 this
    simp [hy_ne]
    ring

/-- The fixed points are exactly a and b -/
theorem flipInvolution_fixed_iff (x : ℝ) :
  flipInvolution hab x = x ↔ x = a ∨ x = b := by
  unfold flipInvolution
  constructor
  · -- Forward direction
    intro hfix
    by_cases h : x = a ∨ x = b
    · exact h
    · push_neg at h
      simp [h] at hfix
      -- From a + b - x = x, we get x = (a + b)/2
      have : x = (a + b) / 2 := by linarith
      -- But (a + b)/2 is strictly between a and b
      have h_mid : a < (a + b) / 2 ∧ (a + b) / 2 < b := by
        constructor <;> linarith
      -- This contradicts that x must be a or b
      exfalso
      -- We've shown x = (a+b)/2, which is neither a nor b
      have : x ≠ a ∧ x ≠ b := by
        rw [this]
        constructor
        · intro heq
          have : a = (a + b) / 2 := heq
          linarith
        · intro heq
          have : b = (a + b) / 2 := heq.symm
          linarith
      exact h this
  · -- Backward direction
    intro h
    cases h with
    | inl ha => simp [ha]
    | inr hb => simp [hb]

/-- The standard involution with fixed points at 0 and φ -/
def standardInvolution : ℝ → ℝ :=
  flipInvolution (by rw [φ]; norm_num : 0 < φ)

theorem standardInvolution_involutive : Function.Involutive standardInvolution :=
  flipInvolution_involutive _

theorem standardInvolution_fixed_iff (x : ℝ) :
  standardInvolution x = x ↔ x = 0 ∨ x = φ := by
  exact flipInvolution_fixed_iff _ x

/-- For the recognition fixed points theorem, use the standard involution -/
theorem recognition_fixed_points_solution :
  ∃ J : ℝ → ℝ, (∀ x, J (J x) = x) ∧
  (∃ vacuum phi_state : ℝ, vacuum ≠ phi_state ∧
   J vacuum = vacuum ∧ J phi_state = phi_state ∧
   ∀ x, J x = x → x = vacuum ∨ x = phi_state) := by
  use standardInvolution
  constructor
  · exact standardInvolution_involutive
  · use 0, φ
    constructor
    · -- 0 ≠ φ
      have : φ > 0 := by rw [φ]; norm_num
      linarith
    constructor
    · -- J(0) = 0
      rw [standardInvolution_fixed_iff]
      left; rfl
    constructor
    · -- J(φ) = φ
      rw [standardInvolution_fixed_iff]
      right; rfl
    · -- Any fixed point is 0 or φ
      exact standardInvolution_fixed_iff

end RecognitionScience.Helpers
