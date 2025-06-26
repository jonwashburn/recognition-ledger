/-
  Mass Formula Investigation
  =========================

  Testing alternative formulas to resolve the catastrophic mass prediction failures.
  Current formula E_r = E_coh × φ^r gives errors up to 100x.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RecognitionScience.MassInvestigation

open Real

-- Constants
def E_coh : ℝ := 0.090  -- eV
def φ : ℝ := (1 + sqrt 5) / 2
def m_e : ℝ := 0.000511  -- GeV (electron mass)
def m_p : ℝ := 0.938272  -- GeV (proton mass)
def α : ℝ := 1/137.036  -- Fine structure constant

-- Experimental masses (in GeV)
def exp_masses : List (String × ℝ × ℕ) := [
  ("electron", 0.000511, 32),
  ("muon", 0.105658, 39),
  ("tau", 1.77686, 44),
  ("up", 0.0022, 33),
  ("down", 0.0047, 34),
  ("strange", 0.093, 38),
  ("charm", 1.27, 40),
  ("bottom", 4.18, 45),
  ("top", 172.7, 47),
  ("W", 80.379, 52),
  ("Z", 91.1876, 53),
  ("Higgs", 125.25, 58)
]

-- Original formula (problematic)
def mass_original (r : ℕ) : ℝ :=
  (E_coh / 1e9) * φ^r

-- Alternative 1: Modular formula
def mass_modular (r : ℕ) : ℝ :=
  let base_mass := m_e * φ^((r - 32) % 8)
  let octave_factor := 1 + (r - 32) / 8 * α
  base_mass * octave_factor

-- Alternative 2: Logarithmic scaling
def mass_log (r : ℕ) : ℝ :=
  m_e * exp ((r - 32 : ℝ) * log φ / 8)

-- Alternative 3: Inverse for heavy particles
def mass_inverse (r : ℕ) : ℝ :=
  if r < 40 then
    m_e * φ^(r - 32)
  else
    m_p / φ^(r - 40)

-- Alternative 4: Hybrid with binding energy
def binding_energy (r : ℕ) : ℝ :=
  E_coh * log (1 + r) / (r + 1)

def mass_with_binding (r : ℕ) : ℝ :=
  let bare_mass := (E_coh / 1e9) * φ^r
  bare_mass - binding_energy r / 1e9

-- Alternative 5: Dressed mass with running
def dressed_mass (r : ℕ) : ℝ :=
  let bare_mass := (E_coh / 1e9) * φ^r
  let Λ := 1e19  -- Planck scale in eV
  bare_mass * (1 + α * log (Λ * 1e-9 / bare_mass))

-- Calculate percentage error
def percent_error (predicted observed : ℝ) : ℝ :=
  abs (predicted - observed) / observed * 100

-- Test a formula against all experimental masses
def test_formula (formula : ℕ → ℝ) (name : String) : IO Unit := do
  IO.println s!"\n=== Testing {name} ==="
  IO.println "Particle    | Rung | Predicted | Observed | Error %"
  IO.println "------------|------|-----------|----------|--------"

  let mut total_error := 0.0
  let mut count := 0

  for (particle, obs_mass, rung) in exp_masses do
    let pred_mass := formula rung
    let error := percent_error pred_mass obs_mass
    total_error := total_error + error
    count := count + 1

    -- Format output
    let particle_pad := String.mk (List.replicate (12 - particle.length) ' ')
    let pred_str := s!"{pred_mass:.6}".take 9
    let obs_str := s!"{obs_mass:.6}".take 8
    let error_str := s!"{error:.1}"

    IO.println s!"{particle}{particle_pad}| {rung}   | {pred_str} | {obs_str} | {error_str}"

  let avg_error := total_error / count.toFloat
  IO.println s!"\nAverage error: {avg_error:.1}%"

  -- Check if this meets our success criteria
  if avg_error < 5.0 then
    IO.println "✓ SUCCESS: Average error < 5%"
  else
    IO.println "✗ FAIL: Average error > 5%"

-- Alternative 6: Recognition-scale modulation
def recognition_scale (r : ℕ) : ℝ :=
  let τ_r := τ₀ * φ^((r - 32) / 8)
  let scale_factor := 1 / (1 + τ_r / τ₀)
  m_e * φ^(r - 32) * scale_factor
  where τ₀ := 7.33e-15  -- seconds

-- Alternative 7: Eight-beat quantization
def mass_eightbeat (r : ℕ) : ℝ :=
  let phase := (r - 32) % 8
  let octave := (r - 32) / 8
  let base := m_e * (1 + phase * E_coh / 0.511)
  base * (1 + octave * sqrt α)

-- Main test routine
def main : IO Unit := do
  IO.println "MASS FORMULA INVESTIGATION"
  IO.println "========================="

  -- Test all formulas
  test_formula mass_original "Original (E_coh × φ^r)"
  test_formula mass_modular "Modular (φ^(r%8) × octaves)"
  test_formula mass_log "Logarithmic (exp(r×ln(φ)/8))"
  test_formula mass_inverse "Inverse (m_p/φ^r for heavy)"
  test_formula mass_with_binding "With Binding Energy"
  test_formula dressed_mass "Dressed (with running)"
  test_formula recognition_scale "Recognition Scale"
  test_formula mass_eightbeat "Eight-beat Quantized"

  IO.println "\n=== ANALYSIS ==="
  IO.println "The original formula fails catastrophically."
  IO.println "We need to find which alternative matches experiment."

  -- Special test for leptons only
  IO.println "\n=== LEPTON-ONLY TEST ==="
  let leptons := [("electron", 0.000511, 32), ("muon", 0.105658, 39), ("tau", 1.77686, 44)]

  for formula in [mass_modular, mass_log, mass_eightbeat] do
    let mut lepton_error := 0.0
    for (_, obs, r) in leptons do
      lepton_error := lepton_error + percent_error (formula r) obs
    IO.println s!"Average lepton error: {lepton_error / 3:.2}%"

-- Run the investigation
#eval main

/-!
## Next Steps Based on Results

1. If any formula gives <5% average error → implement it
2. If modular/eightbeat work for leptons → investigate quark corrections
3. If all fail → rederive rung assignments from quantum numbers
4. Consider that rungs might not be sequential integers
-/

end RecognitionScience.MassInvestigation
