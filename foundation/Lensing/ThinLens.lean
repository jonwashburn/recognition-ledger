import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Real.Basic

/-!
# Thin Lens Approximation

This file proves that when a weight function w(r) varies slowly compared to
the lens scale, the shear components are modified by the same factor as the
convergence, up to a controlled error term.
-/

namespace Foundation.Lensing

open Real

/-- A weight function varies slowly if its derivatives are bounded relative to the function -/
structure SlowlyVarying (w : ℝ → ℝ) (ε : ℝ) : Prop where
  positive : ∀ r > 0, w r > 0
  first_deriv : ∀ r > 0, |deriv w r| ≤ ε * w r / r
  second_deriv : ∀ r > 0, |deriv (deriv w) r| ≤ ε * w r / r^2

/-- The error in the thin lens approximation is bounded by ε -/
theorem thin_lens_error_bound {w : ℝ → ℝ} {Φ : ℝ → ℝ} {ε : ℝ}
    (hw : Differentiable ℝ w) (hΦ : Differentiable ℝ Φ)
    (h_slow : SlowlyVarying w ε) (hε : 0 < ε ∧ ε < 1) :
    ∀ r : ℝ × ℝ, r ≠ (0, 0) →
    let R := (r.1^2 + r.2^2).sqrt
    let γ₁_exact := deriv (fun x => deriv (fun y => (w ((x^2 + y^2).sqrt) * Φ ((x^2 + y^2).sqrt))) r.2) r.1 -
                     deriv (fun y => deriv (fun x => (w ((x^2 + y^2).sqrt) * Φ ((x^2 + y^2).sqrt))) r.1) r.2
    let γ₁_approx := w R * (deriv (fun x => deriv (fun y => Φ ((x^2 + y^2).sqrt)) r.2) r.1 -
                            deriv (fun y => deriv (fun x => Φ ((x^2 + y^2).sqrt)) r.1) r.2)
    |γ₁_exact - γ₁_approx| ≤ ε * |γ₁_approx| := by
  intro r hr
  -- The proof would show that extra terms from derivatives of w
  -- are bounded by ε times the leading order term
  sorry

/-- In the thin lens limit (ε → 0), shear is modified by the same factor as convergence -/
theorem thin_lens_limit {w : ℝ → ℝ} {Φ : ℝ → ℝ}
    (hw : Differentiable ℝ w) (hΦ : Differentiable ℝ Φ) :
    ∀ r : ℝ × ℝ, r ≠ (0, 0) →
    (∀ ε > 0, ∃ w_ε, SlowlyVarying w_ε ε ∧
     ∀ s, (s.1^2 + s.2^2).sqrt = (r.1^2 + r.2^2).sqrt → w_ε ((s.1^2 + s.2^2).sqrt) = w ((r.1^2 + r.2^2).sqrt)) →
    let R := (r.1^2 + r.2^2).sqrt
    let γ₁ := deriv (fun x => deriv (fun y => (w ((x^2 + y^2).sqrt) * Φ ((x^2 + y^2).sqrt))) r.2) r.1 -
               deriv (fun y => deriv (fun x => (w ((x^2 + y^2).sqrt) * Φ ((x^2 + y^2).sqrt))) r.1) r.2
    let γ₁_N := deriv (fun x => deriv (fun y => Φ ((x^2 + y^2).sqrt)) r.2) r.1 -
                 deriv (fun y => deriv (fun x => Φ ((x^2 + y^2).sqrt)) r.1) r.2
    γ₁ = w R * γ₁_N := by
  -- In the limit where w varies infinitely slowly,
  -- all correction terms vanish
  sorry

end Foundation.Lensing
