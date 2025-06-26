#!/usr/bin/env python3
"""
Test LNAL vs MOND with proper mass-to-light ratio fitting
This is crucial for fair comparison!
"""

import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import os
from scipy.optimize import minimize_scalar

# Physical constants
G = 4.302e-6  # kpc km^2 s^-2 M_sun^-1
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
a0 = 3.7e-4  # (km/s)²/kpc - standard value

def lnal_transition(x):
    """LNAL transition function F(x) = (1 + exp(-x^φ))^(-1/φ)"""
    x_safe = np.clip(x, 1e-10, 1e10)
    exp_arg = -np.power(x_safe, PHI)
    exp_arg = np.clip(exp_arg, -100, 100)
    return np.power(1 + np.exp(exp_arg), -1/PHI)

def mond_interpolation(x):
    """Standard MOND interpolation function μ(x) = x/√(1+x²)"""
    return x / np.sqrt(1 + x**2)

def load_galaxy(filename):
    """Load SPARC galaxy data"""
    df = pd.read_csv(filename, comment='#', sep='\s+',
                     names=['rad', 'vobs', 'verr', 'vgas', 'vdisk', 'vbul', 'sbdisk', 'sbbul'])
    mask = (df['rad'] > 0) & (df['vobs'] > 0) & (df['verr'] > 0)
    df = df[mask].reset_index(drop=True)
    name = os.path.basename(filename).replace('_rotmod.dat', '')
    return name, df

def fit_galaxy(filename, use_lnal=True):
    """Fit galaxy with optimal mass-to-light ratio"""
    name, df = load_galaxy(filename)
    
    r = df['rad'].values  # kpc
    v_obs = df['vobs'].values  # km/s
    v_err = df['verr'].values  # km/s
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values  # assumes M/L = 1
    v_bulge = df['vbul'].values
    
    def chi2_function(ml_ratio):
        """Chi-squared as function of disk M/L ratio"""
        # Scale disk velocity by sqrt(M/L)
        v_disk_scaled = v_disk * np.sqrt(ml_ratio)
        v_newton_sq = v_gas**2 + v_disk_scaled**2 + v_bulge**2
        
        # Calculate accelerations
        g_newton = v_newton_sq / r
        x = g_newton / a0
        
        # Apply chosen function
        if use_lnal:
            factor = lnal_transition(x)
        else:
            factor = mond_interpolation(x)
        
        g_modified = g_newton * factor
        v_model = np.sqrt(g_modified * r)
        
        # Chi-squared
        chi2 = np.sum(((v_obs - v_model) / v_err)**2)
        return chi2
    
    # Find optimal M/L ratio (search between 0.1 and 5)
    result = minimize_scalar(chi2_function, bounds=(0.1, 5.0), method='bounded')
    ml_best = result.x
    chi2_best = result.fun / len(v_obs)
    
    # Calculate final model with best M/L
    v_disk_scaled = v_disk * np.sqrt(ml_best)
    v_newton_sq = v_gas**2 + v_disk_scaled**2 + v_bulge**2
    g_newton = v_newton_sq / r
    x = g_newton / a0
    
    if use_lnal:
        factor = lnal_transition(x)
    else:
        factor = mond_interpolation(x)
    
    g_modified = g_newton * factor
    v_model = np.sqrt(g_modified * r)
    
    return {
        'name': name,
        'ml_ratio': ml_best,
        'chi2_reduced': chi2_best,
        'r': r,
        'v_obs': v_obs,
        'v_err': v_err,
        'v_model': v_model,
        'v_newton': np.sqrt(v_newton_sq),
        'x': x,
        'factor': factor
    }

def main():
    print("TESTING LNAL vs MOND WITH PROPER M/L FITTING")
    print("="*70)
    print(f"Using a₀ = {a0:.2e} (km/s)²/kpc")
    print("="*70)
    
    test_files = [
        'Rotmod_LTG/NGC2403_rotmod.dat',
        'Rotmod_LTG/NGC3198_rotmod.dat',
        'Rotmod_LTG/DDO154_rotmod.dat',
        'Rotmod_LTG/NGC6503_rotmod.dat'
    ]
    
    results_lnal = []
    results_mond = []
    
    print("\n{:<12} {:>10} {:>10} {:>10} {:>10} {:>10}".format(
        "Galaxy", "M/L LNAL", "χ²/N LNAL", "M/L MOND", "χ²/N MOND", "Ratio"))
    print("-"*70)
    
    for file in test_files:
        if os.path.exists(file):
            # Fit with LNAL
            res_lnal = fit_galaxy(file, use_lnal=True)
            results_lnal.append(res_lnal)
            
            # Fit with MOND
            res_mond = fit_galaxy(file, use_lnal=False)
            results_mond.append(res_mond)
            
            ratio = res_lnal['chi2_reduced'] / res_mond['chi2_reduced']
            
            print("{:<12} {:>10.2f} {:>10.1f} {:>10.2f} {:>10.1f} {:>10.1f}".format(
                res_lnal['name'],
                res_lnal['ml_ratio'],
                res_lnal['chi2_reduced'],
                res_mond['ml_ratio'],
                res_mond['chi2_reduced'],
                ratio
            ))
    
    # Plot comparisons
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    for i in range(min(4, len(results_lnal))):
        ax = axes[i//2, i%2]
        
        res_l = results_lnal[i]
        res_m = results_mond[i]
        
        # Plot data
        ax.errorbar(res_l['r'], res_l['v_obs'], yerr=res_l['v_err'],
                   fmt='ko', markersize=4, alpha=0.7, label='Data')
        
        # Plot models
        ax.plot(res_l['r'], res_l['v_model'], 'r-', linewidth=2,
                label=f'LNAL (M/L={res_l["ml_ratio"]:.1f}, χ²/N={res_l["chi2_reduced"]:.1f})')
        ax.plot(res_m['r'], res_m['v_model'], 'g--', linewidth=2,
                label=f'MOND (M/L={res_m["ml_ratio"]:.1f}, χ²/N={res_m["chi2_reduced"]:.1f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(res_l['name'])
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('lnal_vs_mond_with_ml.png', dpi=150, bbox_inches='tight')
    print(f"\nSaved: lnal_vs_mond_with_ml.png")
    
    # Summary statistics
    chi2_lnal = [r['chi2_reduced'] for r in results_lnal]
    chi2_mond = [r['chi2_reduced'] for r in results_mond]
    
    print("\n" + "="*70)
    print("SUMMARY WITH FITTED M/L RATIOS:")
    print("="*70)
    print(f"LNAL: Mean χ²/N = {np.mean(chi2_lnal):.1f}")
    print(f"MOND: Mean χ²/N = {np.mean(chi2_mond):.1f}")
    
    if np.mean(chi2_mond) > 0:
        improvement = np.mean(chi2_lnal) / np.mean(chi2_mond)
        if improvement > 1:
            print(f"\nMOND is {improvement:.1f}x better than LNAL")
        else:
            print(f"\nLNAL is {1/improvement:.1f}x better than MOND")
    
    # Check x ranges with fitted M/L
    print("\nTypical x values with fitted M/L:")
    for res in results_mond:
        x_median = np.median(res['x'])
        print(f"{res['name']}: x_median = {x_median:.2f}")
    
    if np.mean(chi2_mond) > 5:
        print("\nBoth models still have poor fits (χ²/N >> 1)")
        print("Need additional physics beyond simple interpolation functions!")

if __name__ == "__main__":
    main() 