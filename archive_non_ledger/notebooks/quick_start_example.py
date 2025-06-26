#!/usr/bin/env python3
"""
Quick Start Example: LNAL Gravity Theory
========================================

This notebook demonstrates how to use the LNAL gravity framework
to fit galaxy rotation curves without dark matter.
"""

import numpy as np
import matplotlib.pyplot as plt
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import LNAL modules
from reproduction.build_sparc_master_table import load_galaxy_data
from reproduction.ledger_final_combined import recognition_weight_combined

# %% Load a single galaxy example
print("Loading example galaxy NGC3198...")

# Load rotation curve data
galaxy_name = 'NGC3198'
data_path = '../data/Rotmod_LTG/NGC3198_rotmod.dat'

# Read the data
data = np.loadtxt(data_path)
r = data[:, 0]  # radius in kpc
v_obs = data[:, 1]  # observed velocity in km/s
v_err = data[:, 2]  # velocity error
v_gas = data[:, 3]  # gas component
v_disk = data[:, 4]  # disk component
v_bul = data[:, 5] if data.shape[1] > 5 else np.zeros_like(r)  # bulge

# %% Calculate LNAL prediction

# Paper parameters
params_global = [0.194, 5.064, 2.953, 0.216, 0.3]  # α, C₀, γ, δ, h_z/R_d
lambda_norm = 0.119

# Galaxy properties (typical values for demonstration)
galaxy_data = {
    'r': r,
    'v_obs': v_obs,
    'T_dyn': 2 * np.pi * r / v_obs * 1e6,  # dynamical time in years
    'f_gas_true': 0.15,  # gas fraction
    'Sigma_0': 1e8,  # central surface brightness
    'R_d': 3.0,  # disk scale length
}

# Simple profile for demonstration
params_profile = [1.0, 3.0, 5.0, 8.0]  # n(r) control points
hyperparams = [0.003, 0.032]  # smoothness, prior strength

# Calculate recognition weight
w, n_r, zeta = recognition_weight_combined(
    r, galaxy_data, params_global, params_profile, hyperparams
)

# LNAL velocity prediction
v_newton = np.sqrt(v_gas**2 + v_disk**2 + v_bul**2)
v_lnal = np.sqrt(lambda_norm * w) * v_newton

# %% Visualize results

plt.figure(figsize=(10, 8))

# Main plot
plt.subplot(2, 1, 1)
plt.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=5, 
             label='Observed', capsize=3, alpha=0.8)
plt.plot(r, v_newton, 'b--', linewidth=2, label='Newtonian', alpha=0.7)
plt.plot(r, v_lnal, 'r-', linewidth=2.5, label='LNAL Gravity')

plt.xlabel('Radius [kpc]', fontsize=12)
plt.ylabel('Velocity [km/s]', fontsize=12)
plt.title(f'{galaxy_name} Rotation Curve - LNAL Gravity Theory', fontsize=14)
plt.legend(fontsize=11)
plt.grid(True, alpha=0.3)

# Recognition weight
plt.subplot(2, 1, 2)
plt.plot(r, w * lambda_norm, 'g-', linewidth=2)
plt.fill_between(r, 0, w * lambda_norm, alpha=0.3, color='green')
plt.axhline(y=1, color='k', linestyle=':', alpha=0.5)

plt.xlabel('Radius [kpc]', fontsize=12)
plt.ylabel('Recognition Weight w(r)', fontsize=12)
plt.title('Bandwidth-Limited Gravity Enhancement', fontsize=14)
plt.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('../results/quick_start_example.png', dpi=150, bbox_inches='tight')
plt.show()

# %% Print key insights

print("\nKey Insights from LNAL Gravity:")
print("="*50)
print(f"1. Maximum recognition weight: {np.max(w * lambda_norm):.2f}×")
print(f"2. Average boost factor: {np.mean(w * lambda_norm):.2f}×")
print(f"3. No dark matter required!")
print(f"4. All effects emerge from bandwidth constraints")

# Calculate goodness of fit
chi2 = np.sum(((v_obs - v_lnal) / v_err)**2) / len(v_obs)
print(f"\nGoodness of fit: χ²/N = {chi2:.3f}")

print("\nTo reproduce the full 0.48 fit across 175 galaxies:")
print("  cd ../reproduction")
print("  python reproduce_048_fit.py") 