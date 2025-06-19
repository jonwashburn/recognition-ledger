/-
Recognition Science - Universal Mass Formula Test
===============================================

This file tests the Universal Mass Formula m(n) = M₀ × χ^(n + 7/12)
where χ = φ/π ≈ 0.515 is the optimal recognition scale.
-/

namespace RecognitionScience

-- Constants
def φ : Float := 1.618033988749895
def π : Float := 3.14159265359
def χ : Float := φ / π  -- ≈ 0.515036

def resIndex : Float := 7.0 / 12.0  -- 7/12 ≈ 0.583333

-- Electron calibration
def electron_mass_GeV : Float := 0.000511
def electron_rung : Float := 32.0

-- Calculate M₀ from electron calibration
def M₀ : Float := electron_mass_GeV / (χ ^ (electron_rung + resIndex))

-- Universal Mass Formula
def m_universal (n : Float) : Float := M₀ * (χ ^ (n + resIndex))

-- Test electron mass (should be exact)
def electron_test : Float := m_universal electron_rung
#eval electron_test  -- Should be 0.000511

-- Test muon mass
def muon_rung : Float := 39.0
def muon_test : Float := m_universal muon_rung
#eval muon_test  -- What do we get?

-- Muon/electron ratio
def muon_electron_ratio : Float := muon_test / electron_test
#eval muon_electron_ratio  -- Compare to observed 206.8

-- Test the scaling factor
def chi_power_7 : Float := χ ^ 7.0
#eval chi_power_7  -- χ^7 for muon_rung - electron_rung

-- Test W boson
def W_rung : Float := 52.0
def W_test : Float := m_universal W_rung
#eval W_test  -- Should be ~80.4 GeV

-- Test Z boson
def Z_rung : Float := 53.0
def Z_test : Float := m_universal Z_rung
#eval Z_test  -- Should be ~91.2 GeV

-- Test Higgs
def Higgs_rung : Float := 58.0
def Higgs_test : Float := m_universal Higgs_rung
#eval Higgs_test  -- Should be ~125.1 GeV

-- Key insight: Check if we need to use different base
-- What if we calibrate M₀ differently?

-- Alternative: Direct calculation from source_code.txt Table 32
-- Using the full particle mass table values

def electron_observed : Float := 0.000511  -- GeV
def muon_observed : Float := 0.1057  -- GeV
def tau_observed : Float := 1.777  -- GeV
def W_observed : Float := 80.4  -- GeV
def Z_observed : Float := 91.2  -- GeV
def Higgs_observed : Float := 125.1  -- GeV

-- Check what M₀ would need to be for muon to work
def M₀_for_muon : Float := muon_observed / (χ ^ (muon_rung + resIndex))
#eval M₀_for_muon

-- Check consistency
def ratio_M₀ : Float := M₀_for_muon / M₀
#eval ratio_M₀  -- How much do the M₀ values differ?

-- The issue may be that we need efficiency factors E(d,s,g)
-- Or that the Universal Mass Formula requires additional corrections

end RecognitionScience
