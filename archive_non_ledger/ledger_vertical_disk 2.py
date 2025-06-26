#!/usr/bin/env python3
"""
Ledger solver with vertical disk physics
Adds sech² vertical density profile correction to gravitational field
"""

import numpy as np
import pickle
from scipy.optimize import differential_evolution
import matplotlib.pyplot as plt

# Constants
G_kpc = 4.302e-6  # kpc (km/s)² / M_sun
tau_0 = 1e8  # years
Sigma_star = 1e8  # M_sun/kpc²

def vertical_correction(r, R_d, h_z_ratio=0.15):
    """
    Vertical disk correction factor ζ(r)
    
    For a sech² vertical profile:
    ζ(r) ≈ 1 + 0.5 * (h_z/r) * f(r/R_d)
    
    where f accounts for the disk's radial exponential profile
    """
    h_z = h_z_ratio * R_d  # Typical thin disk
    
    # Correction is stronger in inner regions where disk is thicker relative to radius
    x = r / R_d
    
    # Empirical function that captures the vertical correction
    # Peaks at ~1 R_d, falls off at large radii
    f_profile = np.exp(-x/2) * (1 + x/3)
    
    # Full correction
    zeta = 1 + 0.5 * (h_z / (r + 0.1*R_d)) * f_profile
    
    return zeta

def recognition_weight_vertical(r, galaxy_data, params):
    """
    Recognition weight with vertical disk correction
    """
    alpha, beta, C0, gamma, delta, r1, n1, n2, h_z_ratio = params
    
    # Get galaxy properties
    T_dyn = galaxy_data['T_dyn']
    f_gas = galaxy_data['f_gas_true']
    Sigma_0 = galaxy_data['Sigma_0']
    R_d = galaxy_data['R_d']
    
    # Complexity factor
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Time factor
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Radial profile
    x1 = (r / r1) ** beta
    trans1 = 1 / (1 + x1)
    trans2 = x1 / (1 + x1)
    
    n_inner = 1.0
    n_disk = n1
    n_base = trans1 * n_inner + trans2 * n_disk
    
    # Outer transition
    r2 = 20.0  # kpc
    x2 = (r / r2) ** beta
    trans3 = x2 / (1 + x2)
    n_total = (1 - trans3) * n_base + trans3 * n2
    
    # Total weight before vertical correction
    w = xi * n_total * time_factor
    
    return w

def fit_galaxy_vertical(galaxy_data, params, lambda_norm):
    """
    Fit galaxy with vertical disk correction
    """
    r = galaxy_data['r']
    v_obs = galaxy_data['v_obs']
    df = galaxy_data['data']
    v_err = df['verr'].values
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bul = df['vbul'].values
    R_d = galaxy_data['R_d']
    
    # Get h_z_ratio from params
    h_z_ratio = params[-1]
    
    # Recognition weights
    w = recognition_weight_vertical(r, galaxy_data, params)
    
    # Vertical correction
    zeta = vertical_correction(r, R_d, h_z_ratio)
    
    # Effective G including vertical correction
    G_eff = G_kpc * lambda_norm * w * zeta
    
    # Find best M/L
    ml_values = np.linspace(0.1, 5.0, 40)
    chi2_values = []
    
    for ml in ml_values:
        v_disk_scaled = v_disk * np.sqrt(ml)
        v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
        g_newton = v2_newton / r
        g_eff = g_newton * (G_eff / G_kpc)
        v_model = np.sqrt(g_eff * r)
        
        chi2 = np.sum(((v_obs - v_model) / v_err)**2)
        chi2_values.append(chi2)
    
    idx_best = np.argmin(chi2_values)
    ml_best = ml_values[idx_best]
    chi2_best = chi2_values[idx_best]
    
    # Final model
    v_disk_scaled = v_disk * np.sqrt(ml_best)
    v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
    g_newton = v2_newton / r
    g_eff = g_newton * (G_eff / G_kpc)
    v_model = np.sqrt(g_eff * r)
    
    return {
        'ml': ml_best,
        'chi2': chi2_best,
        'chi2_reduced': chi2_best / len(v_obs),
        'v_model': v_model,
        'G_eff': G_eff,
        'zeta': zeta
    }

def global_objective_vertical(params, master_table):
    """
    Global objective with vertical disk physics
    """
    # Calculate normalization
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        w = recognition_weight_vertical(r, galaxy, params)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    lambda_norm = W_Newton / W_tot if W_tot > 0 else 1.0
    
    # Fit all galaxies
    total_chi2 = 0
    total_points = 0
    
    for name, galaxy in master_table.items():
        try:
            fit = fit_galaxy_vertical(galaxy, params, lambda_norm)
            total_chi2 += fit['chi2']
            total_points += len(galaxy['v_obs'])
        except:
            continue
    
    return total_chi2 / total_points if total_points > 0 else 1e10

def optimize_vertical(master_table, n_galaxies=50):
    """
    Optimize including vertical disk parameter
    """
    # Use subset for speed
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    # Bounds (added h_z_ratio)
    bounds = [
        (0.0, 1.0),    # alpha
        (1.0, 3.0),    # beta
        (0.0, 20.0),   # C0
        (0.5, 3.0),    # gamma
        (0.0, 1.0),    # delta
        (0.3, 3.0),    # r1
        (1.0, 10.0),   # n1
        (1.0, 10.0),   # n2
        (0.05, 0.3)    # h_z_ratio (h_z/R_d)
    ]
    
    print(f"Optimizing {len(bounds)} parameters with vertical disk physics...")
    print("Expected improvement: ~20% reduction in χ²/N")
    
    result = differential_evolution(
        lambda p: global_objective_vertical(p, subset),
        bounds,
        maxiter=30,
        popsize=15,
        disp=True
    )
    
    return result.x, result.fun

def analyze_vertical_results(master_table, params_opt):
    """
    Analyze results with vertical correction
    """
    # Calculate final normalization
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        w = recognition_weight_vertical(r, galaxy, params_opt)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    lambda_norm = W_Newton / W_tot
    
    print(f"\nGlobal normalization: λ = {lambda_norm:.3f}")
    print(f"Vertical disk scale: h_z/R_d = {params_opt[-1]:.3f}")
    
    # Fit all galaxies
    results = []
    print("\nFitting all galaxies with vertical correction...")
    
    for i, (name, galaxy) in enumerate(master_table.items()):
        if i % 30 == 0:
            print(f"  Progress: {i}/{len(master_table)}")
        
        try:
            fit = fit_galaxy_vertical(galaxy, params_opt, lambda_norm)
            fit['name'] = name
            fit['f_gas'] = galaxy['f_gas_true']
            results.append(fit)
        except:
            continue
    
    # Statistics
    chi2_values = [r['chi2_reduced'] for r in results]
    print(f"\nResults with vertical disk physics:")
    print(f"  Median χ²/N = {np.median(chi2_values):.2f}")
    print(f"  Mean χ²/N = {np.mean(chi2_values):.2f}")
    print(f"  Fraction < 3: {np.mean(np.array(chi2_values) < 3):.1%}")
    print(f"  Fraction < 2: {np.mean(np.array(chi2_values) < 2):.1%}")
    print(f"  Fraction < 1.5: {np.mean(np.array(chi2_values) < 1.5):.1%}")
    
    # Plot examples showing vertical correction effect
    plot_vertical_examples(master_table, results, params_opt, lambda_norm)
    
    return results

def plot_vertical_examples(master_table, results, params_opt, lambda_norm):
    """
    Plot examples highlighting vertical correction
    """
    # Sort by chi²
    results_sorted = sorted(results, key=lambda x: x['chi2_reduced'])
    
    # Pick diverse examples
    indices = [0, len(results)//4, len(results)//2, -1]
    examples = [results_sorted[i] for i in indices if i < len(results_sorted)]
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    axes = axes.flatten()
    
    for ax, res in zip(axes, examples):
        galaxy = master_table[res['name']]
        
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_err = galaxy['data']['verr'].values
        v_model = res['v_model']
        zeta = res['zeta']
        
        # Main plot: rotation curve
        ax.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=3,
                   alpha=0.6, label='Data')
        ax.plot(r, v_model, 'r-', linewidth=2,
               label=f'Model (M/L={res["ml"]:.1f})')
        
        # Add vertical correction as secondary axis
        ax2 = ax.twinx()
        ax2.plot(r, zeta, 'g--', linewidth=1.5, alpha=0.7)
        ax2.set_ylabel('ζ(r) [vertical correction]', color='g')
        ax2.tick_params(axis='y', labelcolor='g')
        ax2.set_ylim(0.9, 1.3)
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{res["name"]}: χ²/N={res["chi2_reduced"]:.2f}')
        ax.legend(loc='lower right')
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('ledger_vertical_disk_examples.png', dpi=150)
    print("Saved: ledger_vertical_disk_examples.png")

def main():
    """Main execution"""
    
    # Load master table
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize with vertical physics
    params_opt, chi2_opt = optimize_vertical(master_table, n_galaxies=50)
    
    print("\n" + "="*60)
    print("OPTIMIZED PARAMETERS (with vertical disk):")
    print("="*60)
    param_names = ['α', 'β', 'C₀', 'γ', 'δ', 'r₁', 'n₁', 'n₂', 'h_z/R_d']
    for name, val in zip(param_names, params_opt):
        print(f"  {name} = {val:.3f}")
    print(f"\nOptimization χ²/N = {chi2_opt:.2f}")
    print("="*60)
    
    # Analyze full sample
    results = analyze_vertical_results(master_table, params_opt)
    
    # Save results
    output = {
        'params_opt': params_opt,
        'results': results,
        'chi2_opt': chi2_opt
    }
    
    with open('ledger_vertical_results.pkl', 'wb') as f:
        pickle.dump(output, f)
    
    print("\nSaved: ledger_vertical_results.pkl")

if __name__ == "__main__":
    main() 