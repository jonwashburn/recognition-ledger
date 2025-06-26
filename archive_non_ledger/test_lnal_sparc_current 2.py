#!/usr/bin/env python3
"""
Test current LNAL formula on SPARC galaxies
Shows exactly how far off we are
"""

import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import glob
import os

# Physical constants
G = 4.302e-6  # kpc km^2 s^-2 M_sun^-1
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
c = 2.998e5  # km/s

# LNAL parameters - use standard MOND value for now
a0_SI = 1.2e-10  # m/s² - standard MOND value
# Convert to galaxy units: 1 kpc = 3.086e19 m, 1 km/s = 1000 m/s
# a [kpc/s²] = a [m/s²] * (1 kpc / 3.086e19 m) * (1000 m/s / 1 km/s)²
# a [kpc/s²] = a [m/s²] * 3.241e-14
a0 = a0_SI * 3.241e-14  # Convert to (km/s)²/kpc units

def lnal_transition(x):
    """LNAL transition function F(x) = (1 + exp(-x^φ))^(-1/φ)"""
    x_safe = np.clip(x, 1e-10, 1e10)
    exp_arg = -np.power(x_safe, PHI)
    exp_arg = np.clip(exp_arg, -100, 100)
    return np.power(1 + np.exp(exp_arg), -1/PHI)

def load_galaxy(filename):
    """Load SPARC galaxy data"""
    # Read data
    df = pd.read_csv(filename, comment='#', sep='\s+',
                     names=['rad', 'vobs', 'verr', 'vgas', 'vdisk', 'vbul', 'sbdisk', 'sbbul'])
    
    # Clean
    mask = (df['rad'] > 0) & (df['vobs'] > 0) & (df['verr'] > 0)
    df = df[mask].reset_index(drop=True)
    
    name = os.path.basename(filename).replace('_rotmod.dat', '')
    
    return name, df

def test_galaxy(filename):
    """Test LNAL on a single galaxy"""
    name, df = load_galaxy(filename)
    
    r = df['rad'].values  # kpc
    v_obs = df['vobs'].values  # km/s
    v_err = df['verr'].values  # km/s
    
    # Newtonian velocity (assuming M/L = 1)
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bulge = df['vbul'].values
    v_newton_sq = v_gas**2 + v_disk**2 + v_bulge**2
    
    # Calculate accelerations
    g_newton = v_newton_sq / r  # (km/s)²/kpc
    
    # Apply LNAL
    g_lnal = g_newton * lnal_transition(g_newton / a0)
    v_lnal = np.sqrt(g_lnal * r)
    
    # Chi-squared
    residuals = (v_obs - v_lnal) / v_err
    chi2 = np.sum(residuals**2)
    chi2_reduced = chi2 / len(v_obs)
    
    # Mean relative error
    rel_error = np.mean(np.abs(v_obs - v_lnal) / v_obs) * 100
    
    return {
        'name': name,
        'r': r,
        'v_obs': v_obs,
        'v_err': v_err,
        'v_newton': np.sqrt(v_newton_sq),
        'v_lnal': v_lnal,
        'chi2': chi2,
        'chi2_reduced': chi2_reduced,
        'rel_error': rel_error,
        'residuals': residuals
    }

def main():
    print("TESTING CURRENT LNAL FORMULA ON SPARC DATA")
    print("="*60)
    print(f"Using a₀ = {a0_SI:.2e} m/s² = {a0:.2e} kpc/s²")
    print(f"Transition function: F(x) = (1 + e^(-x^φ))^(-1/φ)")
    print("="*60)
    
    # Test on a few galaxies
    test_files = [
        'Rotmod_LTG/NGC2403_rotmod.dat',
        'Rotmod_LTG/NGC3198_rotmod.dat',
        'Rotmod_LTG/DDO154_rotmod.dat',
        'Rotmod_LTG/NGC6503_rotmod.dat',
        'Rotmod_LTG/UGC02885_rotmod.dat'
    ]
    
    results = []
    
    for file in test_files:
        if os.path.exists(file):
            result = test_galaxy(file)
            results.append(result)
            
            print(f"\n{result['name']}:")
            print(f"  χ²/N = {result['chi2_reduced']:.1f}")
            print(f"  Mean relative error = {result['rel_error']:.1f}%")
            print(f"  RMS residual = {np.sqrt(np.mean(result['residuals']**2)):.1f}σ")
    
    # Create plot
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    for i, result in enumerate(results):
        if i >= 6:
            break
            
        ax = axes[i]
        
        # Plot data and models
        ax.errorbar(result['r'], result['v_obs'], yerr=result['v_err'],
                   fmt='ko', markersize=4, alpha=0.7, label='Data')
        ax.plot(result['r'], result['v_newton'], 'b--', linewidth=2, label='Newton')
        ax.plot(result['r'], result['v_lnal'], 'r-', linewidth=2, label='LNAL')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f"{result['name']} (χ²/N={result['chi2_reduced']:.0f})")
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Show how far off we are
        ax.text(0.05, 0.95, f"Mean error: {result['rel_error']:.0f}%",
                transform=ax.transAxes, fontsize=10, verticalalignment='top',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
    
    # Hide empty subplot
    if len(results) < 6:
        axes[5].axis('off')
    
    plt.tight_layout()
    plt.savefig('lnal_current_failure.png', dpi=150, bbox_inches='tight')
    print(f"\nSaved: lnal_current_failure.png")
    
    # Summary
    chi2_values = [r['chi2_reduced'] for r in results]
    print("\n" + "="*60)
    print("SUMMARY: LNAL IS FAILING BADLY")
    print("="*60)
    print(f"Mean χ²/N = {np.mean(chi2_values):.1f} (should be ~1)")
    print(f"Mean relative error = {np.mean([r['rel_error'] for r in results]):.0f}%")
    print("\nThe transition function F(x) = (1 + e^(-x^φ))^(-1/φ) is NOT working!")

if __name__ == "__main__":
    main() 