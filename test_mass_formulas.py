#!/usr/bin/env python3
"""
Test alternative mass formulas for Recognition Science
Trying to fix the catastrophic failures in mass predictions
"""

import numpy as np
from math import exp, log, sqrt

# Constants
E_coh = 0.090  # eV
phi = (1 + sqrt(5)) / 2  # Golden ratio
m_e = 0.000511  # GeV (electron mass)
m_p = 0.938272  # GeV (proton mass)
alpha = 1/137.036  # Fine structure constant

# Experimental masses (in GeV) with rung assignments
particles = [
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
    ("Higgs", 125.25, 58),
]

def mass_original(r):
    """Original formula: E_r = E_coh × φ^r"""
    return (E_coh / 1e9) * phi**r

def mass_modular(r):
    """Modular formula with octave scaling"""
    base_mass = m_e * phi**((r - 32) % 8)
    octave_factor = 1 + (r - 32) // 8 * alpha
    return base_mass * octave_factor

def mass_log(r):
    """Logarithmic scaling"""
    return m_e * exp((r - 32) * log(phi) / 8)

def mass_inverse(r):
    """Inverse for heavy particles"""
    if r < 40:
        return m_e * phi**(r - 32)
    else:
        return m_p / phi**(r - 40)

def mass_with_binding(r):
    """Include binding energy correction"""
    bare_mass = (E_coh / 1e9) * phi**r
    binding = E_coh * log(1 + r) / (r + 1) / 1e9
    return bare_mass - binding

def mass_dressed(r):
    """Dressed mass with running coupling"""
    bare_mass = (E_coh / 1e9) * phi**r
    Lambda = 1e19  # Planck scale in eV
    if bare_mass > 0:
        return bare_mass * (1 + alpha * log(Lambda * 1e-9 / bare_mass))
    return bare_mass

def mass_recognition_scale(r):
    """Recognition-scale modulation"""
    tau_0 = 7.33e-15  # seconds
    tau_r = tau_0 * phi**((r - 32) / 8)
    scale_factor = 1 / (1 + tau_r / tau_0)
    return m_e * phi**(r - 32) * scale_factor

def mass_eightbeat(r):
    """Eight-beat quantized formula"""
    phase = (r - 32) % 8
    octave = (r - 32) // 8
    base = m_e * (1 + phase * E_coh / 0.511)
    return base * (1 + octave * sqrt(alpha))

def mass_residue_corrected(r):
    """New: Residue arithmetic correction"""
    # Base mass from golden ratio
    base = m_e * phi**(r - 32)
    # Corrections from gauge residues
    color_factor = 1 + 0.1 * (r % 3)
    isospin_factor = 1 + 0.05 * ((r + 1) % 4)
    hypercharge_factor = 1 + 0.02 * ((r + 2) % 6)
    return base * color_factor * isospin_factor * hypercharge_factor

def mass_phase_locked(r):
    """New: Phase-locked with 8-beat"""
    # Each octave is a complete 8-beat cycle
    octave = (r - 32) // 8
    phase = (r - 32) % 8
    # Mass grows linearly with octave, phase modulates
    phase_factor = 1 + 0.2 * np.sin(2 * np.pi * phase / 8)
    return m_e * (2**octave) * phase_factor

def test_formula(formula, name):
    """Test a formula against experimental data"""
    print(f"\n{'='*60}")
    print(f"Testing: {name}")
    print(f"{'='*60}")
    print(f"{'Particle':<12} {'Rung':<6} {'Predicted':<12} {'Observed':<12} {'Error %':<10}")
    print(f"{'-'*60}")
    
    total_error = 0
    lepton_error = 0
    lepton_count = 0
    
    for particle, obs_mass, rung in particles:
        pred_mass = formula(rung)
        if pred_mass > 0 and obs_mass > 0:
            error = abs(pred_mass - obs_mass) / obs_mass * 100
        else:
            error = 999.9
        
        total_error += error
        
        if particle in ["electron", "muon", "tau"]:
            lepton_error += error
            lepton_count += 1
        
        print(f"{particle:<12} {rung:<6} {pred_mass:<12.6g} {obs_mass:<12.6g} {error:<10.1f}")
    
    avg_error = total_error / len(particles)
    avg_lepton_error = lepton_error / lepton_count if lepton_count > 0 else 999.9
    
    print(f"\nAverage error: {avg_error:.1f}%")
    print(f"Lepton average: {avg_lepton_error:.1f}%")
    
    if avg_error < 5.0:
        print("✓ SUCCESS: Average error < 5%")
    elif avg_lepton_error < 5.0:
        print("✓ PARTIAL SUCCESS: Leptons < 5% error")
    else:
        print("✗ FAIL: Errors too large")
    
    return avg_error, avg_lepton_error

# Test all formulas
formulas = [
    (mass_original, "Original (E_coh × φ^r)"),
    (mass_modular, "Modular (φ^(r%8) × octaves)"),
    (mass_log, "Logarithmic (exp(r×ln(φ)/8))"),
    (mass_inverse, "Inverse (m_p/φ^r for heavy)"),
    (mass_with_binding, "With Binding Energy"),
    (mass_dressed, "Dressed (with running)"),
    (mass_recognition_scale, "Recognition Scale"),
    (mass_eightbeat, "Eight-beat Quantized"),
    (mass_residue_corrected, "Residue Corrected"),
    (mass_phase_locked, "Phase-locked 8-beat"),
]

print("MASS FORMULA INVESTIGATION")
print("=" * 80)

results = []
for formula, name in formulas:
    avg_error, lepton_error = test_formula(formula, name)
    results.append((name, avg_error, lepton_error))

# Summary
print("\n" + "=" * 80)
print("SUMMARY OF RESULTS")
print("=" * 80)
print(f"{'Formula':<40} {'Avg Error':<15} {'Lepton Error':<15}")
print("-" * 80)

best_overall = min(results, key=lambda x: x[1])
best_leptons = min(results, key=lambda x: x[2])

for name, avg_err, lep_err in sorted(results, key=lambda x: x[1]):
    marker = ""
    if name == best_overall[0]:
        marker += " ← BEST OVERALL"
    if name == best_leptons[0] and name != best_overall[0]:
        marker += " ← BEST LEPTONS"
    print(f"{name:<40} {avg_err:<15.1f} {lep_err:<15.1f}{marker}")

print("\n" + "=" * 80)
print("CONCLUSIONS:")
print("=" * 80)
print(f"1. Original formula fails catastrophically (>{best_overall[1]:.0f}x worse)")
print(f"2. Best overall: {best_overall[0]} ({best_overall[1]:.1f}% error)")
print(f"3. Best for leptons: {best_leptons[0]} ({best_leptons[2]:.1f}% error)")

if best_overall[1] < 5.0:
    print("\n✓ SUCCESS: Found a formula with <5% average error!")
    print("Next step: Derive this formula from first principles")
else:
    print("\n✗ FAILURE: No formula achieves <5% error")
    print("Next steps:")
    print("1. Reconsider rung assignments")
    print("2. Look for additional correction factors")
    print("3. Consider non-integer rungs")
    print("4. Investigate if mass ratios follow φ better than absolute masses") 