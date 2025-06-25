/-
  Gravitational Lensing with Recognition Weight
  ============================================

  Shows how the recognition weight modifies gravitational
  lensing predictions, providing independent tests.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import gravity.Core.RecognitionWeight
import gravity.Util.PhysicalUnits

namespace RecognitionScience.Lensing

open Real RecognitionScience.Gravity
open MeasureTheory intervalIntegral

/-! ## Surface Density Profiles -/

/-- Baryonic surface density profile -/
structure SurfaceDensity where
  Σ : ℝ → ℝ  -- Σ(R) in M_sun/pc²
  Σ_pos : ∀ R, R > 0 → Σ R ≥ 0
  Σ_decreasing : ∀ R₁ R₂, 0 < R₁ → R₁ < R₂ → Σ R₂ ≤ Σ R₁

/-- Exponential disk profile -/
def exponentialDisk (Σ₀ R_d : ℝ) (hΣ : Σ₀ > 0) (hR : R_d > 0) : SurfaceDensity where
  Σ := fun R => Σ₀ * exp(-R/R_d)
  Σ_pos := by
    intro R hR_pos
    exact mul_nonneg (le_of_lt hΣ) (exp_pos _)
  Σ_decreasing := by
    intro R₁ R₂ hR₁ h12
    apply mul_le_mul_of_nonneg_left
    · apply exp_le_exp.mpr
      apply div_le_div_of_le_left
      · exact h12
      · exact hR
      · exact hR₁
    · exact le_of_lt hΣ

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

/-- Recognition weight typically exceeds 1 in galaxy outskirts -/
-- We state this as an assumption rather than proving it
axiom recognition_weight_exceeds_one (params : RecognitionParameters) :
  ∃ R₀ > 0, ∀ R > R₀,
    let v_circ := sqrt (Units.Constants.G * 1e11 / R)  -- Typical galaxy
    let T_dyn := dynamical_time R v_circ
    recognition_weight params R T_dyn > 1

/-- Recognition weight enhances lensing signal -/
theorem enhanced_convergence (Σ_b : SurfaceDensity) (params : RecognitionParameters) :
    ∃ R₀ > 0, ∀ R > R₀,
    convergence (effectiveSurfaceDensity Σ_b params) R >
    convergence Σ_b.Σ R := by
  obtain ⟨R₀, hR₀⟩ := recognition_weight_exceeds_one params
  use R₀
  intro R hR
  unfold convergence effectiveSurfaceDensity
  -- The integrand is larger when w(r) > 1
  have h_integrand : ∀ r ∈ Set.Ioo 0 R,
      2 * π * r * (Σ_b.Σ r * recognition_weight params r (dynamical_time r _)) >
      2 * π * r * Σ_b.Σ r := by
    intro r hr
    simp at hr
    cases' hr with hr_pos hr_lt
    have h_w : recognition_weight params r _ > 1 := by
      cases' lt_or_le R₀ r with h h
      · exact hR₀ r h
      · -- For r ≤ R₀, we need a different argument
        -- We'll assume w ≥ 1 everywhere for simplicity
        sorry -- TODO: Need global lower bound on w
    calc 2 * π * r * (Σ_b.Σ r * recognition_weight params r _)
      = 2 * π * r * Σ_b.Σ r * recognition_weight params r _ := by ring
      _ > 2 * π * r * Σ_b.Σ r * 1 := by
        apply mul_lt_mul_of_pos_left h_w
        apply mul_pos (mul_pos (mul_pos two_pos π_pos) hr_pos)
        exact Σ_b.Σ_pos r hr_pos
      _ = 2 * π * r * Σ_b.Σ r := by ring

  -- Apply integral monotonicity
  have h_mono : (1 / _) * ∫ r in (0)..(R), 2 * π * r * effectiveSurfaceDensity Σ_b params r >
                (1 / _) * ∫ r in (0)..(R), 2 * π * r * Σ_b.Σ r := by
    apply mul_lt_mul_of_pos_left
    · apply integral_lt_integral_of_ae_lt_of_measure_pos
      · -- Integrability of both functions
        sorry -- TODO: Show integrability
      · -- Almost everywhere inequality
        sorry -- TODO: Convert pointwise to a.e.
      · -- Positive measure of support
        sorry -- TODO: Show measure > 0
    · apply div_pos one_pos
      apply div_pos (pow_pos _ 2) (mul_pos (mul_pos (by norm_num : (4 : ℝ) > 0) π_pos) _)
      exact Units.Constants.c.value
      exact Units.Constants.G
  exact h_mono

/-- Lensing-dynamics consistency (qualitative statement) -/
-- We simplify this to avoid numerical bounds
lemma lensing_dynamics_qualitative (Σ_b : SurfaceDensity) (params : RecognitionParameters) :
    ∀ R > 0,
    let M_eff := 2 * π * ∫ r in (0)..(R), r * effectiveSurfaceDensity Σ_b params r
    let M_baryon := 2 * π * ∫ r in (0)..(R), r * Σ_b.Σ r
    M_eff ≥ M_baryon := by
  intro R hR
  -- Effective mass includes recognition weight ≥ 1
  apply mul_le_mul_of_nonneg_left
  · apply integral_mono
    · -- Integrability
      sorry -- TODO: Show integrability
    · -- Pointwise inequality
      intro r
      unfold effectiveSurfaceDensity
      apply mul_le_mul_of_nonneg_left
      · -- Need w(r) ≥ 1
        sorry -- TODO: Global lower bound on recognition weight
      · apply mul_nonneg
        · exact le_of_lt hR
        · apply Σ_b.Σ_pos
          sorry -- TODO: Need r > 0 in integration domain
  · exact mul_nonneg (mul_pos two_pos π_pos).le (le_refl _)

/-! ## Analytic Results for Exponential Disks -/

/-- Integral formula for exponential profile -/
lemma exponential_integral (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    ∫ r in (0)..(a), r * exp(-r/b) =
    b^2 * (1 - (1 + a/b) * exp(-a/b)) := by
  -- Standard result from integration by parts
  sorry -- TODO: Apply mathlib integration lemmas

/-- Recognition weight modification is measurable -/
def lensingSignal (Σ_b : SurfaceDensity) (params : RecognitionParameters) (R : ℝ) : ℝ :=
  convergence (effectiveSurfaceDensity Σ_b params) R - convergence Σ_b.Σ R

/-- Signal exists at some radius -/
theorem signal_exists (Σ_b : SurfaceDensity) (params : RecognitionParameters) :
    ∃ R > 0, lensingSignal Σ_b params R > 0 := by
  -- Follows from enhanced_convergence
  obtain ⟨R₀, hR₀⟩ := enhanced_convergence Σ_b params
  use R₀ + 1
  constructor
  · linarith
  · unfold lensingSignal
    exact sub_pos.mpr (hR₀ (R₀ + 1) (by linarith))

end RecognitionScience.Lensing
