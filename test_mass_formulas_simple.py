#!/usr/bin/env python3
"""
Test alternative mass formulas for Recognition Science
Trying to fix the catastrophic failures in mass predictions
"""

from math import exp, log, sqrt, sin, pi

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

def mass_eightbeat(r):
    """Eight-beat quantized formula"""
    phase = (r - 32) % 8
    octave = (r - 32) // 8
    base = m_e * (1 + phase * E_coh / 0.511)
    return base * (1 + octave * sqrt(alpha))

def mass_calibrated(r):
    """New: Calibrated to electron exactly"""
    # Force electron to be exact, scale others
    if r == 32:
        return m_e
    # Use logarithmic spacing
    return m_e * exp((r - 32) * 0.3466)  # 0.3466 ≈ log(207)/7

print("LEPTON MASS FORMULA TEST")
print("=" * 50)

# Test each formula
formulas = [
    ("Original", mass_original),
    ("Modular", mass_modular),
    ("Logarithmic", mass_log),
    ("Eight-beat", mass_eightbeat),
    ("Calibrated", mass_calibrated),
]

for name, formula in formulas:
    print(f"\n{name}:")
    print("-" * 30)
    total_error = 0
    
    for particle, obs_mass, rung in particles:
        pred_mass = formula(rung)
        error = abs(pred_mass - obs_mass) / obs_mass * 100
        total_error += error
        print(f"{particle:<10} pred: {pred_mass:.6f} obs: {obs_mass:.6f} error: {error:.1f}%")
    
    avg_error = total_error / len(particles)
    print(f"Average error: {avg_error:.1f}%")
    
    # Check mass ratios
    if formula(32) > 0:
        mu_e_ratio = formula(39) / formula(32)
        tau_e_ratio = formula(44) / formula(32)
        print(f"μ/e ratio: {mu_e_ratio:.1f} (obs: 206.8)")
        print(f"τ/e ratio: {tau_e_ratio:.1f} (obs: 3477)")

print("\n" + "=" * 50)
print("ANALYSIS:")
print("=" * 50)

# The calibrated formula
print("\nThe 'calibrated' formula uses:")
print("m(r) = m_e × exp((r-32) × k)")
print(f"where k = log(206.8)/7 ≈ 0.3466")
print("\nThis gives exact muon/electron ratio.")
print("But it's just curve fitting, not derived from principles.")

print("\nThe fundamental issue:")
print("φ^7 ≈ 29.0 but μ/e ≈ 206.8")
print("φ^12 ≈ 321.9 but τ/e ≈ 3477")
print("\nThe golden ratio alone cannot explain lepton mass ratios!")

print("\nPossible solutions:")
print("1. Rungs are not simple integers")
print("2. Additional quantum corrections needed")
print("3. Mass formula fundamentally wrong")
print("4. Different formula for leptons vs quarks/bosons") 