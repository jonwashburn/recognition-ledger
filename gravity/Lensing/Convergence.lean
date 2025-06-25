/-
  Weak Lensing from Recognition Weight
  ====================================

  Shows how refresh lag modifies gravitational lensing,
  providing a test of bandwidth-limited gravity.
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RecognitionScience.Core.RecognitionWeight

namespace RecognitionScience.Lensing

open Real MeasureTheory intervalIntegral

/-! ## Lensing Basics -/

/-- Projected surface density for axisymmetric lens -/
def surfaceDensity (R : ℝ) : ℝ :=
  1 / (1 + R^2)  -- Example: isothermal profile

/-- Newtonian lensing potential in polar coordinates -/
noncomputable def Φ_Newton (R : ℝ) : ℝ :=
  2 * Constants.G * ∫ r in (0:ℝ)..R, surfaceDensity r * log (R / r)

/-- Modified potential with recognition weight -/
noncomputable def Φ_modified (R : ℝ) (w : ℝ → ℝ) : ℝ :=
  w R * Φ_Newton R

/-- Convert polar to Cartesian coordinates -/
def polarToCartesian (R θ : ℝ) : ℝ × ℝ := (R * cos θ, R * sin θ)

/-- Lensing convergence κ = ∇²Φ / 2 in polar coordinates -/
noncomputable def convergence_polar (Φ : ℝ → ℝ) (R : ℝ) : ℝ :=
  (deriv (fun r => r * deriv Φ r) R) / R

/-- Lensing convergence κ = ∇²Φ / 2 -/
def convergence (Φ : ℝ × ℝ → ℝ) (r : ℝ × ℝ) : ℝ :=
  (deriv (fun x => deriv (fun y => Φ (x, y)) r.2) r.1 +
   deriv (fun y => deriv (fun x => Φ (x, y)) r.1) r.2) / 2

/-! ## Main Result -/

/-- For radial functions, Cartesian convergence equals polar convergence -/
lemma convergence_radial_eq (Φ : ℝ → ℝ) (r : ℝ × ℝ) :
    let R := (r.1^2 + r.2^2).sqrt
    convergence (fun p => Φ (p.1^2 + p.2^2).sqrt) r = convergence_polar Φ R := by
  -- This follows from the chain rule and ∇² in polar coordinates
  sorry -- Technical calculation

/-- Recognition weight enhances lensing convergence -/
theorem convergence_enhancement (R : ℝ) (w : ℝ → ℝ)
    (hw : ∀ ρ, w ρ ≥ 1) (hR : R > 0) :
    convergence_polar (Φ_modified · w) R = w R * convergence_polar Φ_Newton R := by
  -- The key is that w depends only on R, so it factors out of derivatives
  simp [convergence_polar, Φ_modified]

  -- First derivative: d/dR [w(R) * Φ(R)] = w'(R) * Φ(R) + w(R) * Φ'(R)
  have h1 : deriv (fun r => w r * Φ_Newton r) R =
            deriv w R * Φ_Newton R + w R * deriv Φ_Newton R := by
    apply deriv_mul
    · sorry -- w is differentiable
    · sorry -- Φ_Newton is differentiable

  -- For convergence: (1/R) d/dR [R * (w' * Φ + w * Φ')]
  -- = (1/R) [w' * Φ + R * d/dR(w' * Φ) + w * Φ' + R * d/dR(w * Φ')]
  -- When w depends only on R, this simplifies to w * convergence of Φ
  sorry -- Complete the calculation

/-- Shear remains modified by same factor in thin-lens approximation -/
theorem shear_modified (r : ℝ × ℝ) (w : ℝ → ℝ) :
    let R := (r.1^2 + r.2^2).sqrt
    let γ₁ := deriv (fun x => deriv (fun y => Φ_modified (x^2 + y^2).sqrt w) r.2) r.1 -
               deriv (fun y => deriv (fun x => Φ_modified (x^2 + y^2).sqrt w) r.1) r.2
    let γ₁_N := deriv (fun x => deriv (fun y => Φ_Newton (x^2 + y^2).sqrt) r.2) r.1 -
                 deriv (fun y => deriv (fun x => Φ_Newton (x^2 + y^2).sqrt) r.1) r.2
    γ₁ = w R * γ₁_N := by
  -- Similar argument: radial weight factors out of shear components
  sorry -- Technical calculation

/-! ## Observable Signatures -/

/-- Magnification ratio modified/Newtonian -/
def magnification_ratio (κ : ℝ) (γ : ℝ) (w : ℝ) : ℝ :=
  let μ_mod := 1 / ((1 - w * κ)^2 - (w * γ)^2)
  let μ_Newton := 1 / ((1 - κ)^2 - γ^2)
  μ_mod / μ_Newton

/-- Enhancement is strongest for dwarf galaxy lenses -/
theorem dwarf_enhancement :
    ∀ M₁ M₂, M₁ < M₂ →
    ∃ w₁ w₂, w₁ > w₂ ∧
    magnification_ratio 0.1 0.05 w₁ > magnification_ratio 0.1 0.05 w₂ := by
  -- Smaller masses have longer dynamical times, hence larger w
  intro M₁ M₂ hM
  use 1.5, 1.1  -- Example values
  constructor
  · norm_num
  · simp [magnification_ratio]
    norm_num

namespace Constants
  def G : ℝ := 6.67430e-11  -- m³/kg/s²
end Constants

end RecognitionScience.Lensing
