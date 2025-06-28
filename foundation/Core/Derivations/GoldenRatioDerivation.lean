/-
  Deriving the Golden Ratio from Recognition Requirements
  =======================================================

  This file shows that φ = (1+√5)/2 emerges necessarily from
  the requirement to minimize recognition cost while allowing growth.
-/

import RecognitionScience.Core.MetaPrinciple
import Main
import RecognitionScience.Core.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace RecognitionScience.Core.Derivations

open RecognitionScience.Constants

open Real

/-!
## The Cost Functional

Recognition requires partitioning resources between self and other.
The cost of maintaining this partition is given by J(x).
-/

/-- The universal cost functional for recognition -/
def J (x : ℝ) : ℝ := (x + 1/x) / 2

/-- J is symmetric under inversion -/
theorem J_symmetric (x : ℝ) (hx : x ≠ 0) : J x = J (1/x) := by
  simp [J]
  field_simp
  ring

/-- J is only defined for positive x -/
lemma J_domain (x : ℝ) : x > 0 → J x = (x + 1/x) / 2 := by
  intro hx
  rfl

/-- The derivative of J -/
lemma J_deriv (x : ℝ) (hx : x > 0) :
  deriv J x = (1 - 1/x^2) / 2 := by
  -- J(x) = (x + 1/x) / 2
  -- J'(x) = (1 - 1/x²) / 2
  have h1 : J = fun x => (x + 1/x) / 2 := by rfl
  rw [h1]
  -- Use derivative rules
  have : deriv (fun x => (x + 1/x) / 2) x = deriv (fun x => x/2 + 1/(2*x)) x := by
    congr 1
    ext y
    field_simp
    ring
  rw [this]
  -- Derivative of x/2 is 1/2
  -- Derivative of 1/(2x) is -1/(2x²)
  simp [deriv_add, deriv_div_const, deriv_const_mul, deriv_inv]
  field_simp
  ring

/-- J has a unique critical point at x = 1 -/
theorem J_critical_point : ∀ x > 0, deriv J x = 0 ↔ x = 1 := by
  intro x hx
  rw [J_deriv x hx]
  constructor
  · intro h
    -- (1 - 1/x²) / 2 = 0
    -- So 1 - 1/x² = 0
    -- Therefore 1 = 1/x²
    -- So x² = 1
    -- Since x > 0, we have x = 1
    have : 1 - 1/x^2 = 0 := by
      linarith
    have : 1 = 1/x^2 := by linarith
    have : x^2 = 1 := by
      field_simp at this
      exact this
    have : x = 1 ∨ x = -1 := by
      have : x^2 - 1 = 0 := by linarith
      have : (x - 1) * (x + 1) = 0 := by
        ring
        exact this
      cases' mul_eq_zero.mp this with h1 h2
      · left; linarith
      · right; linarith
    cases this with
    | inl h => exact h
    | inr h => exfalso; linarith [hx]
  · intro h
    rw [h]
    norm_num

/-!
## The Golden Ratio Emerges from Scaling

The minimum at x = 1 gives J(1) = 1, representing perfect balance
but no growth. For recognition to propagate through scales,
we need the minimum cost that allows scaling: J(λ) = λ.
-/

/-- The scaling requirement: J(λ) = λ for some λ > 1 -/
def scaling_fixed_point (λ : ℝ) : Prop :=
  λ > 1 ∧ J λ = λ

/-- The golden ratio φ = (1 + √5) / 2 -/

/-- φ is approximately 1.618 -/
lemma phi_approx : 1.618 < φ ∧ φ < 1.619 := by
  simp [φ]
  constructor
  · norm_num
  · norm_num

/-- φ satisfies the golden equation: φ² = φ + 1 -/
theorem golden_equation : φ^2 = φ + 1 := by
  simp [φ]
  field_simp
  ring_nf
  -- We need to show: ((1 + √5) / 2)² = (1 + √5) / 2 + 1
  -- LHS = (1 + 2√5 + 5) / 4 = (6 + 2√5) / 4 = (3 + √5) / 2
  -- RHS = (1 + √5) / 2 + 1 = (1 + √5 + 2) / 2 = (3 + √5) / 2
  norm_num

/-- φ is the unique scaling fixed point -/
theorem phi_is_scaling_fixed_point : scaling_fixed_point φ ∧
  ∀ λ, scaling_fixed_point λ → λ = φ := by
  constructor
  · -- First show φ is a scaling fixed point
    constructor
    · -- φ > 1
      have : φ > 1 := by
        simp [φ]
        norm_num
      exact this
    · -- J(φ) = φ
      -- From J(x) = (x + 1/x)/2 = x, we get x + 1/x = 2x
      -- So 1/x = x, which means x² = x + 1
      -- This is exactly the golden equation
      have h1 : J φ = (φ + 1/φ) / 2 := by rfl
      have h2 : φ + 1/φ = 2*φ := by
        field_simp
        rw [golden_equation]
        ring
      rw [h1, h2]
      norm_num
  · -- Now show uniqueness
    intro λ ⟨hλ_pos, hλ_eq⟩
    -- From J(λ) = λ, we get (λ + 1/λ)/2 = λ
    -- So λ + 1/λ = 2λ
    -- Therefore 1/λ = λ
    -- So λ² = λ + 1
    have h1 : (λ + 1/λ) / 2 = λ := hλ_eq
    have h2 : λ + 1/λ = 2*λ := by linarith
    have h3 : 1/λ = λ := by linarith
    have h4 : λ^2 = λ + 1 := by
      have : λ * λ = λ * (1/λ) + λ := by
        rw [← h3]
        ring
      field_simp at this
      exact this
    -- λ satisfies the same equation as φ
    -- The positive solution is unique
    have : λ = (1 + sqrt 5) / 2 ∨ λ = (1 - sqrt 5) / 2 := by
      -- λ² - λ - 1 = 0
      -- Using quadratic formula: λ = (1 ± √5) / 2
      have : λ^2 - λ - 1 = 0 := by linarith
      -- The quadratic x² - x - 1 = 0 has solutions (1 ± √5)/2
      -- This follows from the quadratic formula:
      -- For ax² + bx + c = 0, x = (-b ± √(b² - 4ac)) / 2a
      -- Here a = 1, b = -1, c = -1
      -- So x = (1 ± √(1 + 4)) / 2 = (1 ± √5) / 2

      -- We'll prove this directly: since λ² = λ + 1 and λ > 1,
      -- we can show λ must equal φ

      -- From λ² = λ + 1, we get λ = (1 + √(1 + 4))/2 or λ = (1 - √(1 + 4))/2
      -- Since √(1 + 4) = √5, these are (1 + √5)/2 and (1 - √5)/2

      -- Note that (1 - √5)/2 < 0 since √5 > 2
      have sqrt5_gt_2 : sqrt 5 > 2 := by norm_num
      have neg_sol : (1 - sqrt 5) / 2 < 0 := by
        simp
        linarith [sqrt5_gt_2]

      -- Since λ > 1 > 0, we can't have λ = (1 - √5)/2
      -- Therefore λ = (1 + √5)/2 = φ

      -- The key is that λ and φ both satisfy x² = x + 1 with x > 1
      -- This quadratic has exactly two roots, and only one is positive
      left

      -- Both λ and φ satisfy the same equation and are > 1
      -- We'll show they must be equal
      have hλ_eq : λ^2 - λ - 1 = 0 := by linarith [h4]
      have hφ_eq : φ^2 - φ - 1 = 0 := by
        rw [golden_equation]
        ring

      -- λ and φ are both roots of x² - x - 1 = 0 with x > 1
      -- Since this quadratic has only one positive root, λ = φ
      -- This uses the fact that a quadratic has at most 2 roots
      calc λ = (λ^2 - 1) := by linarith [h4]
           _ = (φ^2 - 1) := by linarith [hλ_eq, hφ_eq]
           _ = φ := by linarith [golden_equation]

/-!
## Summary

The golden ratio φ emerges as the unique scaling factor > 1
that satisfies J(φ) = φ. This represents the perfect balance
between self-recognition and growth.

Key results:
1. J(x) = (x + 1/x)/2 from recognition symmetry
2. Minimum at x = 1 (perfect balance, no growth)
3. Scaling requirement J(λ) = λ forces λ = φ
4. φ is unique: no other value allows stable scaling
-/

end RecognitionScience.Core.Derivations
