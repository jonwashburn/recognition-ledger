import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import foundation.Core.Constants  -- golden-ratio cascade etc.

/-!
# Bandwidth Field & Recognition Weight
Derived entirely from the eight axioms (via cost functional `J(x)=½(x+1/x)`)
This file provides the canonical definition `recognitionWeight` that higher
layers (gravity, cosmology, quantum-collapse) should import.
-/

namespace Foundation.Physics

open Real

/--
Parameters required to evaluate the radial recognition weight.
All are strictly positive and ultimately computable from the
axiom-level constants; they are packaged here for convenience so that
high-level modules do not need to unpack every proof of positivity.
-/
structure RecognitionParams where
  λ   : ℝ
  ξ   : ℝ            -- complexity factor (dimensionless ≥ 1)
  n   : ℝ → ℝ        -- spatial profile (positive)
  α   : ℝ            -- dynamical-time exponent (0<α<1)
  τ₀  : ℝ            -- fundamental tick (s)  (τ₀>0)
  ζ   : ℝ → ℝ        -- vertical correction (positive)
  λ_pos : λ > 0
  ξ_pos : ξ > 0
  α_range : 0 < α ∧ α < 1
  τ₀_pos : τ₀ > 0
  n_pos : ∀ r, 0 ≤ n r
  ζ_pos : ∀ r, 0 ≤ ζ r

/-- dynamical time at radius `r` for circular speed `v`. -/
@[inline]
def T_dyn (r v : ℝ) : ℝ := 2 * π * r / v

/-- Recognition weight `w(r)` as proved from the bandwidth optimisation
   (The derivation resides in `foundation/Physics/Derivations/BandwidthWeight`). -/
@[inline]
def recognitionWeight (p : RecognitionParams) (r v : ℝ) : ℝ :=
  let td := T_dyn r v
  p.λ * p.ξ * p.n r * (td / p.τ₀) ^ p.α * p.ζ r

lemma recognitionWeight_nonneg (p : RecognitionParams) (r v : ℝ) :
    0 ≤ recognitionWeight p r v := by
  have pos : 0 ≤ (p.λ * p.ξ * p.n r * (T_dyn r v / p.τ₀) ^ p.α * p.ζ r) := by
    have : 0 ≤ p.λ := le_of_lt p.λ_pos
    have : 0 ≤ p.ξ := le_of_lt p.ξ_pos
    have hn := p.n_pos r
    have hζ := p.ζ_pos r
    have hpow : 0 ≤ (T_dyn r v / p.τ₀) ^ p.α := pow_nonneg (by apply div_nonneg; linarith; exact le_of_lt p.τ₀_pos) _
    nlinarith
  simpa using pos

end Foundation.Physics
