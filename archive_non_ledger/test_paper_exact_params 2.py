#!/usr/bin/env python3
"""
Test the exact parameters from the paper
"""

import numpy as np
from lnal_bandwidth_triage_model import load_sparc_data, fit_galaxy
import json

# Exact parameters from the paper
PAPER_PARAMS = {
    'alpha': 0.194,
    'C0': 5.064,
    'gamma': 2.953,
    'delta': 0.216,
    'lambda_norm': 0.119
}

print("Testing with exact paper parameters:")
for k, v in PAPER_PARAMS.items():
    print(f"  {k} = {v}")

# Load data
print("\nLoading SPARC data from Rotmod_LTG...")
sparc_data = load_sparc_data()

# Fit all galaxies with paper parameters
all_results = []
chi2_values = []

print(f"\nFitting {len(sparc_data)} galaxies...")
for i, (galaxy_name, galaxy_data) in enumerate(sparc_data.items()):
    if i % 20 == 0:
        print(f"  Progress: {i}/{len(sparc_data)}")
    
    result = fit_galaxy(galaxy_name, galaxy_data, PAPER_PARAMS)
    if result is not None:
        all_results.append(result)
        chi2_values.append(result['chi2_reduced'])

chi2_values = np.array(chi2_values)

# Statistics
print("\n" + "="*60)
print("RESULTS WITH EXACT PAPER PARAMETERS")
print("="*60)
print(f"Galaxies analyzed: {len(chi2_values)}")
print(f"Median χ²/N: {np.median(chi2_values):.3f}")
print(f"Mean χ²/N: {np.mean(chi2_values):.3f}")
print(f"Best χ²/N: {np.min(chi2_values):.3f}")
print(f"Worst χ²/N: {np.max(chi2_values):.3f}")
print(f"\nFraction with χ²/N < 0.5: {np.sum(chi2_values < 0.5)/len(chi2_values)*100:.1f}%")
print(f"Fraction with χ²/N < 1.0: {np.sum(chi2_values < 1.0)/len(chi2_values)*100:.1f}%")
print(f"Fraction with χ²/N < 1.5: {np.sum(chi2_values < 1.5)/len(chi2_values)*100:.1f}%")
print(f"Fraction with χ²/N < 2.0: {np.sum(chi2_values < 2.0)/len(chi2_values)*100:.1f}%")

# Check if we're close to paper's claim
if np.median(chi2_values) < 0.5:
    print("\n✓ Successfully reproduced paper's median χ²/N < 0.5!")
else:
    print(f"\n✗ Median χ²/N = {np.median(chi2_values):.3f} vs paper's 0.48")

# Save detailed results
results_summary = {
    'parameters': PAPER_PARAMS,
    'statistics': {
        'n_galaxies': len(chi2_values),
        'median_chi2': float(np.median(chi2_values)),
        'mean_chi2': float(np.mean(chi2_values)),
        'std_chi2': float(np.std(chi2_values)),
        'min_chi2': float(np.min(chi2_values)),
        'max_chi2': float(np.max(chi2_values)),
        'frac_below_0.5': float(np.sum(chi2_values < 0.5)/len(chi2_values)),
        'frac_below_1.0': float(np.sum(chi2_values < 1.0)/len(chi2_values)),
        'frac_below_1.5': float(np.sum(chi2_values < 1.5)/len(chi2_values)),
        'frac_below_2.0': float(np.sum(chi2_values < 2.0)/len(chi2_values))
    }
}

with open('paper_params_test_results.json', 'w') as f:
    json.dump(results_summary, f, indent=2)

print("\nResults saved to paper_params_test_results.json") 