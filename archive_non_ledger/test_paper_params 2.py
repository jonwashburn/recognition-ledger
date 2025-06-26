#!/usr/bin/env python3
"""Test bandwidth triage model with exact paper parameters"""

import numpy as np
from lnal_bandwidth_triage_model import load_sparc_data, fit_galaxy

# Exact parameters from the paper
PAPER_PARAMS = {
    'alpha': 0.194,
    'C0': 5.064,
    'gamma': 2.953,
    'delta': 0.216,
    'lambda_norm': 0.119
}

def test_paper_params():
    # Load data
    print("Loading SPARC data...")
    sparc_data = load_sparc_data()
    
    print(f"\nTesting with paper parameters:")
    for k, v in PAPER_PARAMS.items():
        print(f"  {k} = {v}")
    
    # Test on all galaxies
    chi2_values = []
    for galaxy_name, galaxy_data in sparc_data.items():
        result = fit_galaxy(galaxy_name, galaxy_data, PAPER_PARAMS)
        if result is not None:
            chi2_values.append(result['chi2_reduced'])
    
    chi2_values = np.array(chi2_values)
    
    # Statistics
    print(f"\n{'='*60}")
    print("RESULTS WITH PAPER PARAMETERS")
    print(f"{'='*60}")
    print(f"Galaxies analyzed: {len(chi2_values)}")
    print(f"Median χ²/N: {np.median(chi2_values):.3f}")
    print(f"Mean χ²/N: {np.mean(chi2_values):.3f}")
    print(f"Best χ²/N: {np.min(chi2_values):.3f}")
    print(f"Worst χ²/N: {np.max(chi2_values):.3f}")
    print(f"\nFraction with χ²/N < 0.5: {np.sum(chi2_values < 0.5)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 1.0: {np.sum(chi2_values < 1.0)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 1.5: {np.sum(chi2_values < 1.5)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 2.0: {np.sum(chi2_values < 2.0)/len(chi2_values)*100:.1f}%")
    
    # Separate by galaxy type (using velocity as proxy for mass)
    dwarf_chi2 = []
    spiral_chi2 = []
    
    for i, (galaxy_name, galaxy_data) in enumerate(sparc_data.items()):
        if i < len(chi2_values):
            curve = galaxy_data.get('curve')
            if curve:
                v_max = np.max(curve.get('V_obs', [0]))
                if v_max < 100:  # Rough dwarf criterion
                    dwarf_chi2.append(chi2_values[i])
                else:
                    spiral_chi2.append(chi2_values[i])
    
    if dwarf_chi2:
        print(f"\nDwarf galaxies (V_max < 100 km/s):")
        print(f"  Number: {len(dwarf_chi2)}")
        print(f"  Median χ²/N: {np.median(dwarf_chi2):.3f}")
    
    if spiral_chi2:
        print(f"\nSpiral galaxies (V_max ≥ 100 km/s):")
        print(f"  Number: {len(spiral_chi2)}")
        print(f"  Median χ²/N: {np.median(spiral_chi2):.3f}")

if __name__ == "__main__":
    test_paper_params() 