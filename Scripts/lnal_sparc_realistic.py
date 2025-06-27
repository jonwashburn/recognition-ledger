#!/usr/bin/env python3
"""
Realistic LNAL SPARC Analysis
Properly handles mass-to-light ratios and SPARC data format
"""

import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import os
import glob
from scipy.optimize import minimize

# Physical constants
G = 4.302e-6  # kpc km^2 s^-2 M_sun^-1
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
a0_MOND = 1.2e-10  # m/s^2 - standard MOND value
a0_kpc = a0_MOND * 3.086e16 / 1e6  # Convert to kpc/s^2

# Recognition lengths
L1 = 0.97  # kpc
L2 = 24.3  # kpc

def lnal_transition(x, power=PHI):
    """LNAL transition function F(x) = (1 + exp(-x^φ))^(-1/φ)"""
    # Protect against overflow
    x_safe = np.clip(x, 1e-10, 1e10)
    exp_arg = -np.power(x_safe, power)
    exp_arg = np.clip(exp_arg, -100, 100)  # Prevent overflow
    return np.power(1 + np.exp(exp_arg), -1/power)

def load_galaxy(filename):
    """Load galaxy data from SPARC format"""
    # Read header for distance
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith('# Distance'):
                distance = float(line.split('=')[1].split('Mpc')[0].strip())
                break
    
    # Read data
    df = pd.read_csv(filename, comment='#', sep='\s+',
                     names=['rad', 'vobs', 'verr', 'vgas', 'vdisk', 'vbul', 'sbdisk', 'sbbul'])
    
    # Clean data
    mask = (df['rad'] > 0) & (df['vobs'] > 0) & (df['verr'] > 0)
    df = df[mask].reset_index(drop=True)
    
    name = os.path.basename(filename).replace('_rotmod.dat', '')
    
    return {
        'name': name,
        'distance': distance,
        'df': df
    }

def calculate_rotation_curve(galaxy, ml_disk, ml_bulge=None):
    """Calculate rotation curve with given mass-to-light ratios"""
    df = galaxy['df']
    r = df['rad'].values
    
    # Gas contribution (no M/L needed)
    v_gas = df['vgas'].values
    
    # Disk contribution with M/L
    # The SPARC data gives velocities assuming M/L = 1
    # So we scale by sqrt(M/L)
    v_disk = df['vdisk'].values * np.sqrt(ml_disk)
    
    # Bulge contribution
    if ml_bulge is not None and 'vbul' in df.columns:
        v_bulge = df['vbul'].values * np.sqrt(ml_bulge)
    else:
        v_bulge = df['vbul'].values
    
    # Total Newtonian velocity
    v_newton_sq = v_gas**2 + v_disk**2 + v_bulge**2
    
    # Calculate accelerations
    g_newton = v_newton_sq / r
    
    # Apply LNAL
    g_lnal = g_newton * lnal_transition(g_newton / a0_kpc)
    v_lnal = np.sqrt(g_lnal * r)
    
    return {
        'r': r,
        'v_newton': np.sqrt(v_newton_sq),
        'v_lnal': v_lnal,
        'g_newton': g_newton,
        'g_lnal': g_lnal
    }

def fit_galaxy_ml(galaxy):
    """Fit mass-to-light ratio for best match"""
    df = galaxy['df']
    r = df['rad'].values
    vobs = df['vobs'].values
    verr = df['verr'].values
    
    # Check if galaxy has significant disk component
    has_disk = np.any(df['vdisk'] > 10)
    has_bulge = np.any(df['vbul'] > 10)
    
    def objective(params):
        if has_disk and has_bulge:
            ml_disk, ml_bulge = params
        elif has_disk:
            ml_disk = params[0]
            ml_bulge = 1.0
        else:
            ml_disk = 1.0
            ml_bulge = params[0] if has_bulge else 1.0
        
        # Calculate model
        result = calculate_rotation_curve(galaxy, ml_disk, ml_bulge)
        v_model = result['v_lnal']
        
        # Chi-squared
        residuals = (vobs - v_model) / verr
        return np.sum(residuals**2)
    
    # Initial guess and bounds for M/L ratios
    # Typical values: 0.2-2.0 for disks, 2.0-8.0 for bulges
    if has_disk and has_bulge:
        x0 = [0.5, 4.0]
        bounds = [(0.1, 2.0), (1.0, 10.0)]
    elif has_disk:
        x0 = [0.5]
        bounds = [(0.1, 2.0)]
    elif has_bulge:
        x0 = [4.0]
        bounds = [(1.0, 10.0)]
    else:
        # No significant stellar component
        x0 = [1.0]
        bounds = [(0.5, 2.0)]
    
    # Optimize
    result = minimize(objective, x0, bounds=bounds, method='L-BFGS-B')
    
    # Extract best-fit parameters
    if has_disk and has_bulge:
        ml_disk, ml_bulge = result.x
    elif has_disk:
        ml_disk = result.x[0]
        ml_bulge = 1.0
    else:
        ml_disk = 1.0
        ml_bulge = result.x[0] if has_bulge else 1.0
    
    # Calculate final model
    final_result = calculate_rotation_curve(galaxy, ml_disk, ml_bulge)
    final_result['vobs'] = vobs
    final_result['verr'] = verr
    
    # Statistics
    residuals = (vobs - final_result['v_lnal']) / verr
    chi2 = np.sum(residuals**2)
    dof = len(vobs) - len(result.x)
    chi2_reduced = chi2 / dof
    
    final_result['ml_disk'] = ml_disk
    final_result['ml_bulge'] = ml_bulge
    final_result['chi2'] = chi2
    final_result['chi2_reduced'] = chi2_reduced
    final_result['residuals'] = residuals
    final_result['relative_residuals'] = (vobs - final_result['v_lnal']) / final_result['v_lnal']
    
    return final_result

def analyze_sample():
    """Analyze a sample of SPARC galaxies"""
    
    # Get galaxy files
    files = glob.glob('Rotmod_LTG/*_rotmod.dat')
    files = [f for f in files if ' 2' not in f]
    
    # Analyze first 20 galaxies
    sample_files = files[:20]
    
    print("Realistic LNAL SPARC Analysis")
    print("="*60)
    print(f"Analyzing {len(sample_files)} galaxies with fitted M/L ratios")
    print(f"Using a₀ = {a0_MOND:.2e} m/s² = {a0_kpc:.2e} kpc/s²")
    print("="*60)
    
    results = []
    
    for i, file in enumerate(sample_files):
        try:
            # Load galaxy
            galaxy = load_galaxy(file)
            
            # Fit with M/L optimization
            fit = fit_galaxy_ml(galaxy)
            
            # Store results
            results.append({
                'name': galaxy['name'],
                'fit': fit,
                'galaxy': galaxy
            })
            
            # Print summary
            print(f"\n{galaxy['name']}:")
            print(f"  M/L disk: {fit['ml_disk']:.2f}")
            print(f"  M/L bulge: {fit['ml_bulge']:.2f}")
            print(f"  χ²/ν: {fit['chi2_reduced']:.2f}")
            print(f"  Mean residual: {np.mean(fit['relative_residuals'])*100:.1f}%")
            
        except Exception as e:
            print(f"Error with {file}: {e}")
    
    # Summary statistics
    chi2_values = [r['fit']['chi2_reduced'] for r in results]
    ml_disk_values = [r['fit']['ml_disk'] for r in results]
    
    print("\n" + "="*60)
    print("SUMMARY STATISTICS")
    print("="*60)
    print(f"Median χ²/ν: {np.median(chi2_values):.2f}")
    print(f"Mean χ²/ν: {np.mean(chi2_values):.2f} ± {np.std(chi2_values):.2f}")
    print(f"Good fits (χ²/ν < 3): {sum(1 for x in chi2_values if x < 3)}/{len(chi2_values)}")
    print(f"Mean M/L disk: {np.mean(ml_disk_values):.2f} ± {np.std(ml_disk_values):.2f}")
    
    # Create visualization
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    
    # Plot 6 example galaxies
    indices = [np.argmin(chi2_values),  # Best fit
               np.argmax(chi2_values),  # Worst fit
               len(chi2_values)//4,     # Random examples
               len(chi2_values)//2,
               3*len(chi2_values)//4,
               -1]
    
    for idx, i in enumerate(indices):
        if i >= len(results):
            continue
            
        ax = axes[idx//3, idx%3]
        
        result = results[i]
        fit = result['fit']
        galaxy = result['galaxy']
        
        # Plot data and models
        ax.errorbar(fit['r'], fit['vobs'], yerr=fit['verr'],
                   fmt='ko', markersize=4, alpha=0.7, label='Data')
        ax.plot(fit['r'], fit['v_newton'], 'b--', linewidth=2, 
                label=f'Newton (M/L={fit["ml_disk"]:.1f})')
        ax.plot(fit['r'], fit['v_lnal'], 'r-', linewidth=2, label='LNAL')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f"{galaxy['name']} (χ²/ν={fit['chi2_reduced']:.1f})")
        ax.legend(fontsize=8)
        ax.set_xscale('log')
        ax.grid(True, alpha=0.3)
        
        # Add text with residual info
        mean_res = np.mean(fit['relative_residuals']) * 100
        ax.text(0.05, 0.05, f'Mean res: {mean_res:.1f}%',
                transform=ax.transAxes, fontsize=8)
    
    plt.tight_layout()
    plt.savefig('lnal_sparc_realistic.png', dpi=150, bbox_inches='tight')
    print(f"\nSaved: lnal_sparc_realistic.png")
    
    # Check residual patterns
    all_residuals = []
    all_relative_residuals = []
    all_accelerations = []
    
    for result in results:
        fit = result['fit']
        all_residuals.extend(fit['residuals'])
        all_relative_residuals.extend(fit['relative_residuals'])
        all_accelerations.extend(fit['g_lnal'])
    
    all_residuals = np.array(all_residuals)
    all_relative_residuals = np.array(all_relative_residuals)
    all_accelerations = np.array(all_accelerations)
    
    # Residual analysis plot
    fig2, axes2 = plt.subplots(2, 2, figsize=(12, 10))
    
    # Residual distribution
    ax = axes2[0, 0]
    ax.hist(all_residuals, bins=30, alpha=0.7, density=True)
    x = np.linspace(-5, 5, 100)
    ax.plot(x, np.exp(-x**2/2)/np.sqrt(2*np.pi), 'r-', linewidth=2)
    ax.set_xlabel('Residuals (σ)')
    ax.set_ylabel('Density')
    ax.set_title('Residual Distribution')
    ax.set_xlim(-5, 5)
    
    # Relative residuals vs acceleration
    ax = axes2[0, 1]
    ax.scatter(np.log10(all_accelerations/a0_kpc), all_relative_residuals*100,
              alpha=0.3, s=10)
    ax.axhline(0, color='k', linestyle='--', alpha=0.5)
    ax.set_xlabel('log(g/a₀)')
    ax.set_ylabel('Relative Residual (%)')
    ax.set_title('Residuals vs Acceleration')
    ax.set_ylim(-50, 50)
    ax.grid(True, alpha=0.3)
    
    # Mean residual per galaxy
    ax = axes2[1, 0]
    mean_residuals = [np.mean(r['fit']['relative_residuals'])*100 for r in results]
    ax.hist(mean_residuals, bins=15, alpha=0.7, edgecolor='black')
    ax.axvline(0, color='k', linestyle='--', alpha=0.5)
    ax.set_xlabel('Mean Relative Residual per Galaxy (%)')
    ax.set_ylabel('Count')
    ax.set_title(f'Mean: {np.mean(mean_residuals):.1f}%')
    
    # Chi-squared distribution
    ax = axes2[1, 1]
    ax.hist(chi2_values, bins=15, alpha=0.7, edgecolor='black')
    ax.axvline(1, color='r', linestyle='--', alpha=0.5, label='χ²/ν=1')
    ax.set_xlabel('Reduced χ²')
    ax.set_ylabel('Count')
    ax.set_title('Fit Quality Distribution')
    ax.legend()
    
    plt.tight_layout()
    plt.savefig('lnal_sparc_residuals.png', dpi=150, bbox_inches='tight')
    print(f"Saved: lnal_sparc_residuals.png")
    
    # Final statistics
    print("\n" + "="*60)
    print("RESIDUAL ANALYSIS")
    print("="*60)
    print(f"RMS residual: {np.sqrt(np.mean(all_residuals**2)):.2f}σ")
    print(f"Mean relative residual: {np.mean(all_relative_residuals)*100:.1f}%")
    print(f"Fraction positive residuals: {np.sum(all_relative_residuals > 0)/len(all_relative_residuals):.3f}")
    
    return results

if __name__ == "__main__":
    results = analyze_sample() 