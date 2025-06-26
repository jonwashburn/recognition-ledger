#!/usr/bin/env python3
"""
Debug LNAL SPARC analysis - understand high chi-squared values
"""

import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import os
import glob

# Physical constants
G = 4.302e-6  # kpc km^2 s^-2 M_sun^-1
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
a0 = 1.2e-10 * 3.086e13 / 1e3**2  # m/s^2 to kpc/s^2

def lnal_transition(x):
    """LNAL transition function"""
    return np.power(1 + np.exp(-np.power(x, PHI)), -1/PHI)

def load_and_analyze_galaxy(filename):
    """Load and analyze a single galaxy"""
    
    # Read data
    df = pd.read_csv(filename, comment='#', delim_whitespace=True,
                     names=['rad', 'vobs', 'verr', 'vgas', 'vdisk', 'vbul', 'sbdisk', 'sbbul'])
    
    # Clean data
    mask = (df['rad'] > 0) & (df['vobs'] > 0) & (df['verr'] > 0)
    df = df[mask].reset_index(drop=True)
    
    # Calculate Newtonian velocity
    v_newton_sq = df['vgas']**2 + df['vdisk']**2 + df['vbul']**2
    v_newton = np.sqrt(v_newton_sq)
    
    # Calculate accelerations
    r = df['rad'].values
    g_newton = v_newton_sq.values / r
    
    # Apply LNAL
    g_lnal = g_newton * lnal_transition(g_newton / a0)
    v_lnal = np.sqrt(g_lnal * r)
    
    # Calculate chi-squared
    vobs = df['vobs'].values
    verr = df['verr'].values
    
    residuals = (vobs - v_lnal) / verr
    chi2 = np.sum(residuals**2)
    chi2_reduced = chi2 / len(vobs)
    
    return {
        'name': os.path.basename(filename).replace('_rotmod.dat', ''),
        'r': r,
        'vobs': vobs,
        'verr': verr,
        'v_newton': v_newton,
        'v_lnal': v_lnal,
        'chi2': chi2,
        'chi2_reduced': chi2_reduced,
        'n_points': len(vobs),
        'residuals': residuals,
        'relative_residuals': (vobs - v_lnal) / v_lnal
    }

def main():
    """Debug analysis"""
    
    # Test on a few galaxies
    files = glob.glob('Rotmod_LTG/*_rotmod.dat')
    files = [f for f in files if ' 2' not in f][:10]  # First 10 galaxies
    
    print("Debugging LNAL SPARC Analysis")
    print("="*50)
    
    # Analyze each galaxy
    results = []
    for file in files:
        try:
            result = load_and_analyze_galaxy(file)
            results.append(result)
            print(f"\n{result['name']}:")
            print(f"  Points: {result['n_points']}")
            print(f"  χ²/ν: {result['chi2_reduced']:.2f}")
            print(f"  Mean |residual|: {np.mean(np.abs(result['residuals'])):.2f}")
            print(f"  Mean relative residual: {np.mean(result['relative_residuals'])*100:.1f}%")
            
            # Check for outliers
            outliers = np.abs(result['residuals']) > 5
            if np.any(outliers):
                print(f"  Outliers: {np.sum(outliers)} points with |residual| > 5σ")
                
        except Exception as e:
            print(f"Error with {file}: {e}")
    
    # Create diagnostic plots
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    
    # Pick best and worst fits
    chi2_values = [r['chi2_reduced'] for r in results]
    best_idx = np.argmin(chi2_values)
    worst_idx = np.argmax(chi2_values)
    median_idx = np.argsort(chi2_values)[len(chi2_values)//2]
    
    for idx, (label, result_idx) in enumerate([('Best', best_idx), 
                                               ('Median', median_idx), 
                                               ('Worst', worst_idx)]):
        result = results[result_idx]
        
        # Top row: Rotation curves
        ax = axes[0, idx]
        ax.errorbar(result['r'], result['vobs'], yerr=result['verr'], 
                   fmt='ko', markersize=4, alpha=0.7, label='Observed')
        ax.plot(result['r'], result['v_newton'], 'b:', linewidth=2, label='Newton')
        ax.plot(result['r'], result['v_lnal'], 'r-', linewidth=2, label='LNAL')
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f"{label}: {result['name']} (χ²/ν={result['chi2_reduced']:.1f})")
        ax.legend()
        ax.set_xscale('log')
        
        # Bottom row: Residuals
        ax = axes[1, idx]
        ax.axhline(0, color='k', linestyle='--', alpha=0.5)
        ax.errorbar(result['r'], result['residuals'], yerr=1, 
                   fmt='o', markersize=4, alpha=0.7)
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Residuals (σ)')
        ax.set_xscale('log')
        ax.set_ylim(-10, 10)
        
        # Add residual statistics
        rms_residual = np.sqrt(np.mean(result['residuals']**2))
        ax.text(0.05, 0.95, f'RMS: {rms_residual:.2f}σ', 
                transform=ax.transAxes, verticalalignment='top')
    
    plt.tight_layout()
    plt.savefig('lnal_sparc_debug.png', dpi=150, bbox_inches='tight')
    print(f"\nSaved: lnal_sparc_debug.png")
    
    # Check error distribution
    print("\n" + "="*50)
    print("ERROR ANALYSIS")
    print("="*50)
    
    # Collect all residuals
    all_residuals = []
    all_verr = []
    all_vobs = []
    for result in results:
        all_residuals.extend(result['residuals'])
        all_verr.extend(result['verr'])
        all_vobs.extend(result['vobs'])
    
    all_residuals = np.array(all_residuals)
    all_verr = np.array(all_verr)
    all_vobs = np.array(all_vobs)
    
    print(f"Total data points: {len(all_residuals)}")
    print(f"Mean residual: {np.mean(all_residuals):.3f}σ")
    print(f"RMS residual: {np.sqrt(np.mean(all_residuals**2)):.3f}σ")
    print(f"Median |residual|: {np.median(np.abs(all_residuals)):.3f}σ")
    
    # Check if errors are underestimated
    print(f"\nTypical velocity error: {np.median(all_verr):.1f} km/s")
    print(f"Typical velocity: {np.median(all_vobs):.1f} km/s")
    print(f"Relative error: {np.median(all_verr/all_vobs)*100:.1f}%")
    
    # Distribution of residuals
    fig2, ax = plt.subplots(1, 1, figsize=(8, 6))
    ax.hist(all_residuals, bins=50, alpha=0.7, density=True, label='Data')
    
    # Overlay normal distribution
    x = np.linspace(-10, 10, 100)
    ax.plot(x, np.exp(-x**2/2)/np.sqrt(2*np.pi), 'r-', linewidth=2, label='N(0,1)')
    
    ax.set_xlabel('Residuals (σ)')
    ax.set_ylabel('Density')
    ax.set_title('Distribution of Residuals')
    ax.legend()
    ax.set_xlim(-10, 10)
    
    plt.savefig('lnal_residual_distribution.png', dpi=150, bbox_inches='tight')
    print(f"\nSaved: lnal_residual_distribution.png")
    
    # Check for systematic effects
    print("\n" + "="*50)
    print("SYSTEMATIC EFFECTS")
    print("="*50)
    
    # Are errors correlated with velocity?
    from scipy.stats import pearsonr
    
    r_corr, p_val = pearsonr(all_vobs, np.abs(all_residuals))
    print(f"Correlation between v_obs and |residual|: r={r_corr:.3f}, p={p_val:.3e}")
    
    # Are errors typically positive?
    positive_fraction = np.sum(all_residuals > 0) / len(all_residuals)
    print(f"Fraction of positive residuals: {positive_fraction:.3f}")
    
    return results

if __name__ == "__main__":
    results = main() 