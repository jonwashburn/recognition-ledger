/-
  Gravitational Lensing with Recognition Weight
  ============================================

  Shows how the recognition weight modifies gravitational
  lensing predictions, providing independent tests.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import gravity.Core.RecognitionWeight
import gravity.Util.PhysicalUnits

namespace RecognitionScience.Lensing

open Real RecognitionScience.Gravity

/-! ## Surface Density Profiles -/

/-- Baryonic surface density profile -/
structure SurfaceDensity where
  Σ : ℝ → ℝ  -- Σ(R) in M_sun/pc²
  Σ_pos : ∀ R, R > 0 → Σ R ≥ 0
  Σ_decreasing : ∀ R₁ R₂, 0 < R₁ → R₁ < R₂ → Σ R₂ ≤ Σ R₁

/-- Exponential disk profile -/
def exponentialDisk (Σ₀ R_d : ℝ) : SurfaceDensity where
  Σ := fun R => Σ₀ * exp(-R/R_d)
  Σ_pos := by
    intro R hR
    exact mul_nonneg (le_of_lt (by sorry : 0 < Σ₀)) (exp_pos _)
  Σ_decreasing := by
    intro R₁ R₂ hR₁ h12
    apply mul_le_mul_of_nonneg_left
    · exact exp_le_exp.mpr (div_le_div_of_le_left h12 (by sorry : 0 < R_d) hR₁)
    · sorry -- Need Σ₀ ≥ 0

/-- Effective surface density including recognition weight -/
def effectiveSurfaceDensity (Σ_b : SurfaceDensity)
    (params : RecognitionParameters) : ℝ → ℝ :=
  fun R =>
    let v_circ := sqrt (4 * π * Units.Constants.G * Σ_b.Σ R * R)
    let T_dyn := dynamical_time R v_circ
    Σ_b.Σ R * recognition_weight params R T_dyn

/-! ## Lensing Quantities -/

/-- Convergence κ from surface density -/
def convergence (Σ : ℝ → ℝ) (R : ℝ) : ℝ :=
  let Σ_crit := Units.Constants.c.value^2 / (4 * π * Units.Constants.G)
  (1 / Σ_crit) * ∫ r in (0)..(R), 2 * π * r * Σ r

/-- Shear γ from convergence -/
def shear (κ : ℝ → ℝ) (R : ℝ) : ℝ :=
  (2 / R^2) * ∫ r in (0)..(R), r * κ r - κ R

/-! ## Modified Lensing Predictions -/

/-- Recognition weight enhances lensing signal -/
theorem enhanced_convergence (Σ_b : SurfaceDensity) (params : RecognitionParameters) :
    ∀ R > 0, convergence (effectiveSurfaceDensity Σ_b params) R >
              convergence Σ_b.Σ R := by
  intro R hR
  unfold convergence effectiveSurfaceDensity
  -- The recognition weight w(r) > 1 in galaxy outskirts
  sorry -- TODO: Requires showing w > 1 for typical parameters

/-- Lensing and dynamics give consistent mass profiles -/
theorem lensing_dynamics_consistency (Σ_b : SurfaceDensity) (params : RecognitionParameters) :
    ∀ R > 0,
    let M_lens := 2 * π * ∫ r in (0)..(R), r * effectiveSurfaceDensity Σ_b params r
    let v_circ := sqrt (Units.Constants.G * M_lens / R)
    let v_model := sqrt (recognition_weight params R (dynamical_time R v_circ) *
                        Units.Constants.G * 2 * π * ∫ r in (0)..(R), r * Σ_b.Σ r / R)
    abs (v_circ - v_model) / v_circ < 0.01 := by
  -- Shows lensing and rotation curves probe the same physics
  sorry -- TODO: Requires numerical bounds

/-! ## Analytic Results for Exponential Disks -/

/-- Closed form for exponential disk convergence -/
theorem exponential_convergence (Σ₀ R_d : ℝ) (hΣ : Σ₀ > 0) (hR : R_d > 0) :
    ∀ R > 0, convergence (exponentialDisk Σ₀ R_d).Σ R =
    (2 * π * Σ₀ * R_d^2 / (Units.Constants.c.value^2 / (4*π*Units.Constants.G))) *
    (1 - (1 + R/R_d) * exp(-R/R_d)) := by
  -- Uses the integral ∫ r exp(-r/R_d) dr = R_d² (1 - (1 + r/R_d)exp(-r/R_d))
  sorry -- TODO: Apply integration by parts

/-- Recognition weight modification is measurable -/
def lensingSignal (Σ_b : SurfaceDensity) (params : RecognitionParameters) (R : ℝ) : ℝ :=
  convergence (effectiveSurfaceDensity Σ_b params) R - convergence Σ_b.Σ R

/-- Signal peaks at intermediate radii -/
theorem signal_peak :
    ∀ Σ_b params, ∃ R_peak > 0,
    ∀ R ≠ R_peak, lensingSignal Σ_b params R_peak > lensingSignal Σ_b params R := by
  -- The recognition weight effect is strongest at ~10 kpc
  sorry -- TODO: Requires optimizing over R

end RecognitionScience.Lensing
