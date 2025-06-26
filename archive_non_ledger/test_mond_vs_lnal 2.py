#!/usr/bin/env python3
"""
Compare MOND interpolation vs LNAL transition function on SPARC data
"""

import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import os

# Physical constants
G = 4.302e-6  # kpc km^2 s^-2 M_sun^-1
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
# Correct conversion: a0 = 1.2e-10 m/s² = 1.2e-10 * (3.086e16)/(1e3)² kpc/(km/s)²
a0 = 1.2e-10 * 3.086e13 / 1e6  # Convert m/s² to (km/s)²/kpc
# This gives a0 ≈ 3.7e-4 (km/s)²/kpc

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

def test_both_functions(filename):
    """Test both LNAL and MOND on a galaxy"""
    name, df = load_galaxy(filename)
    
    r = df['rad'].values  # kpc
    v_obs = df['vobs'].values  # km/s
    v_err = df['verr'].values  # km/s
    
    # Newtonian velocity
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bulge = df['vbul'].values
    v_newton_sq = v_gas**2 + v_disk**2 + v_bulge**2
    
    # Calculate accelerations
    g_newton = v_newton_sq / r  # (km/s)²/kpc
    x = g_newton / a0
    
    # LNAL prediction
    F_lnal = lnal_transition(x)
    g_lnal = g_newton * F_lnal
    v_lnal = np.sqrt(g_lnal * r)
    
    # MOND prediction
    mu_mond = mond_interpolation(x)
    g_mond = g_newton * mu_mond
    v_mond = np.sqrt(g_mond * r)
    
    # Chi-squared for both
    chi2_lnal = np.sum(((v_obs - v_lnal) / v_err)**2) / len(v_obs)
    chi2_mond = np.sum(((v_obs - v_mond) / v_err)**2) / len(v_obs)
    
    # Relative errors
    rel_err_lnal = np.mean(np.abs(v_obs - v_lnal) / v_obs) * 100
    rel_err_mond = np.mean(np.abs(v_obs - v_mond) / v_obs) * 100
    
    return {
        'name': name,
        'r': r,
        'v_obs': v_obs,
        'v_err': v_err,
        'v_newton': np.sqrt(v_newton_sq),
        'v_lnal': v_lnal,
        'v_mond': v_mond,
        'chi2_lnal': chi2_lnal,
        'chi2_mond': chi2_mond,
        'rel_err_lnal': rel_err_lnal,
        'rel_err_mond': rel_err_mond,
        'x': x,
        'F_lnal': F_lnal,
        'mu_mond': mu_mond
    }

def main():
    print("COMPARING MOND vs LNAL ON SPARC DATA")
    print("="*70)
    print(f"Using a₀ = {a0:.2e} (km/s)²/kpc")
    print("="*70)
    
    # Test galaxies
    test_files = [
        'Rotmod_LTG/NGC2403_rotmod.dat',
        'Rotmod_LTG/NGC3198_rotmod.dat',
        'Rotmod_LTG/DDO154_rotmod.dat',
        'Rotmod_LTG/NGC6503_rotmod.dat'
    ]
    
    results = []
    
    print("\n{:<12} {:>12} {:>12} {:>12} {:>12}".format(
        "Galaxy", "χ²/N LNAL", "χ²/N MOND", "Err% LNAL", "Err% MOND"))
    print("-"*70)
    
    for file in test_files:
        if os.path.exists(file):
            result = test_both_functions(file)
            results.append(result)
            
            print("{:<12} {:>12.1f} {:>12.1f} {:>12.0f} {:>12.0f}".format(
                result['name'],
                result['chi2_lnal'],
                result['chi2_mond'],
                result['rel_err_lnal'],
                result['rel_err_mond']
            ))
    
    # Create comparison plots
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    for i, result in enumerate(results[:4]):
        ax = axes[i//2, i%2]
        
        # Plot data and models
        ax.errorbar(result['r'], result['v_obs'], yerr=result['v_err'],
                   fmt='ko', markersize=4, alpha=0.7, label='Data')
        ax.plot(result['r'], result['v_newton'], 'b:', linewidth=2, label='Newton')
        ax.plot(result['r'], result['v_lnal'], 'r--', linewidth=2, 
                label=f'LNAL (χ²/N={result["chi2_lnal"]:.0f})')
        ax.plot(result['r'], result['v_mond'], 'g-', linewidth=2, 
                label=f'MOND (χ²/N={result["chi2_mond"]:.0f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(result['name'])
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('mond_vs_lnal_comparison.png', dpi=150, bbox_inches='tight')
    print(f"\nSaved: mond_vs_lnal_comparison.png")
    
    # Plot transition functions
    fig2, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    x_range = np.logspace(-2, 2, 100)
    F_range = lnal_transition(x_range)
    mu_range = mond_interpolation(x_range)
    
    ax1.loglog(x_range, F_range, 'r-', linewidth=2, label='LNAL: F(x)')
    ax1.loglog(x_range, mu_range, 'g-', linewidth=2, label='MOND: μ(x)')
    ax1.loglog(x_range, x_range, 'k:', label='Newtonian (y=x)')
    ax1.set_xlabel('x = g_N/a₀')
    ax1.set_ylabel('Interpolation Function')
    ax1.set_title('Transition Functions')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Show where galaxy data points fall
    ax2.set_title('Galaxy Data Distribution')
    for result in results:
        ax2.scatter(result['x'], result['mu_mond'], alpha=0.5, s=20)
    ax2.set_xlabel('x = g_N/a₀')
    ax2.set_ylabel('μ(x)')
    ax2.set_xscale('log')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('transition_functions.png', dpi=150, bbox_inches='tight')
    print(f"Saved: transition_functions.png")
    
    # Summary
    print("\n" + "="*70)
    print("SUMMARY:")
    print("="*70)
    
    lnal_chi2 = [r['chi2_lnal'] for r in results]
    mond_chi2 = [r['chi2_mond'] for r in results]
    
    print(f"LNAL: Mean χ²/N = {np.mean(lnal_chi2):.1f}")
    print(f"MOND: Mean χ²/N = {np.mean(mond_chi2):.1f}")
    
    # Debug: check x values
    print("\nDebug - x values (g_N/a₀) range:")
    for result in results:
        x_min, x_max = np.min(result['x']), np.max(result['x'])
        print(f"{result['name']}: {x_min:.2e} to {x_max:.2e}")
    
    # Check if functions differ
    print("\nFunction values at x=0.1:")
    print(f"LNAL: F(0.1) = {lnal_transition(0.1):.4f}")
    print(f"MOND: μ(0.1) = {mond_interpolation(0.1):.4f}")
    
    if np.mean(mond_chi2) > 0:
        print(f"\nMOND is {np.mean(lnal_chi2)/np.mean(mond_chi2):.1f}x better than LNAL!")
    
    if np.mean(mond_chi2) > 5:
        print("\nBut even MOND doesn't work well enough (χ²/N should be ~1)")
        print("Need additional physics beyond simple interpolation functions!")

if __name__ == "__main__":
    main() 