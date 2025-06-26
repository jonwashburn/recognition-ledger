#!/usr/bin/env python3
"""
Unified ledger-refresh solver with global normalization
Uses bandwidth-constrained recognition weights to fit SPARC rotation curves
"""

import numpy as np
import pickle
from scipy.optimize import minimize, minimize_scalar
import matplotlib.pyplot as plt
from pathlib import Path

# Constants
G_kpc = 4.302e-6  # kpc (km/s)² / M_sun
tau_0 = 1e8  # years
Sigma_star = 1e8  # M_sun/kpc²

def recognition_weight(r, T_dyn, f_gas, Sigma_0, params):
    """Calculate normalized recognition weight"""
    alpha, C0, gamma, delta = params
    
    # Complexity factor
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Time-based refresh interval
    n_raw = (T_dyn / tau_0) ** alpha
    
    return xi * n_raw

def fit_single_galaxy(galaxy_data, params, lambda_norm):
    """
    Fit a single galaxy with:
    - Fixed global parameters (alpha, C0, gamma, delta)
    - Fixed global normalization lambda
    - Free stellar M/L ratio
    """
    # Extract data
    r = galaxy_data['r']
    v_obs = galaxy_data['v_obs']
    df = galaxy_data['data']
    v_err = df['verr'].values
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bul = df['vbul'].values
    T_dyn = galaxy_data['T_dyn']
    f_gas = galaxy_data['f_gas_true']
    Sigma_0 = galaxy_data['Sigma_0']
    
    # Calculate recognition weights
    w = recognition_weight(r, T_dyn, f_gas, Sigma_0, params)
    
    # Effective G at each radius
    G_eff = G_kpc * lambda_norm * w
    
    def chi2_ml(ml):
        """Chi-squared as function of M/L"""
        v_disk_scaled = v_disk * np.sqrt(ml)
        v_newton_sq = v_gas**2 + v_disk_scaled**2 + v_bul**2
        g_newton = v_newton_sq / r
        
        # Apply recognition boost
        g_eff = g_newton * (G_eff / G_kpc)
        v_model = np.sqrt(g_eff * r)
        
        chi2 = np.sum(((v_obs - v_model) / v_err)**2)
        return chi2
    
    # Find best M/L
    result = minimize_scalar(chi2_ml, bounds=(0.1, 5.0), method='bounded')
    ml_best = result.x
    chi2_best = result.fun
    chi2_reduced = chi2_best / len(v_obs)
    
    # Calculate final model
    v_disk_scaled = v_disk * np.sqrt(ml_best)
    v_newton_sq = v_gas**2 + v_disk_scaled**2 + v_bul**2
    g_newton = v_newton_sq / r
    g_eff = g_newton * (G_eff / G_kpc)
    v_model = np.sqrt(g_eff * r)
    
    return {
        'ml': ml_best,
        'chi2': chi2_best,
        'chi2_reduced': chi2_reduced,
        'v_model': v_model,
        'G_eff': G_eff,
        'w': w
    }

def global_objective(params, master_table, lambda_norm):
    """
    Calculate total chi² across all galaxies
    with fixed lambda normalization
    """
    total_chi2 = 0
    total_points = 0
    
    for name, galaxy in master_table.items():
        try:
            fit = fit_single_galaxy(galaxy, params, lambda_norm)
            total_chi2 += fit['chi2']
            total_points += len(galaxy['v_obs'])
        except:
            continue
    
    return total_chi2 / total_points if total_points > 0 else 1e10

def optimize_global_parameters(master_table, n_galaxies=30):
    """
    Optimize global parameters with bandwidth constraint:
    1. For each parameter set, calculate required λ
    2. Apply that λ and calculate total chi²
    """
    # Use subset for speed
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    def objective_with_normalization(params):
        """Objective that includes bandwidth normalization"""
        # First calculate required normalization
        from ledger_global_bandwidth import calculate_global_weights
        bandwidth_results = calculate_global_weights(subset, params)
        lambda_norm = bandwidth_results['lambda']
        
        # Then calculate chi² with that normalization
        chi2 = global_objective(params, subset, lambda_norm)
        
        return chi2
    
    # Initial guess
    x0 = [0.5, 2.0, 1.5, 0.3]  # alpha, C0, gamma, delta
    
    # Bounds
    bounds = [
        (0.1, 1.0),   # alpha
        (0.0, 10.0),  # C0
        (0.5, 3.0),   # gamma
        (0.0, 1.0)    # delta
    ]
    
    print(f"Optimizing global parameters on {n_galaxies} galaxies...")
    result = minimize(objective_with_normalization, x0, bounds=bounds, 
                     method='L-BFGS-B', options={'maxiter': 50})
    
    return result.x, result.fun

def analyze_full_sample(master_table, params, lambda_norm):
    """Analyze full SPARC sample with optimized parameters"""
    results = []
    
    print(f"\nAnalyzing {len(master_table)} galaxies...")
    
    for i, (name, galaxy) in enumerate(master_table.items()):
        if i % 20 == 0:
            print(f"  Progress: {i}/{len(master_table)}")
            
        try:
            fit = fit_single_galaxy(galaxy, params, lambda_norm)
            fit['name'] = name
            fit['f_gas'] = galaxy['f_gas_true']
            fit['Sigma_0'] = galaxy['Sigma_0']
            results.append(fit)
        except Exception as e:
            print(f"  Error with {name}: {e}")
            
    return results

def plot_example_fits(master_table, results, params, lambda_norm):
    """Plot example galaxy fits"""
    # Sort by chi²
    results_sorted = sorted(results, key=lambda x: x['chi2_reduced'])
    
    # Pick examples: best, median, worst
    indices = [0, len(results)//2, -1]
    examples = [results_sorted[i] for i in indices]
    
    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    
    for ax, example in zip(axes, examples):
        name = example['name']
        galaxy = master_table[name]
        
        # Data
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        df = galaxy['data']
        v_err = df['verr'].values
        
        # Model
        v_model = example['v_model']
        
        # Plot
        ax.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=4, 
                   alpha=0.7, label='Data')
        ax.plot(r, v_model, 'r-', linewidth=2, 
               label=f'Model (M/L={example["ml"]:.2f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{name}\nχ²/N={example["chi2_reduced"]:.1f}, '
                    f'f_gas={example["f_gas"]:.2f}')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
    plt.tight_layout()
    plt.savefig('ledger_unified_examples.png', dpi=150)
    print("Saved: ledger_unified_examples.png")

def main():
    """Main execution"""
    
    # Load master table
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    # Optimize parameters
    params_opt, chi2_opt = optimize_global_parameters(master_table, n_galaxies=30)
    
    print(f"\nOptimized parameters:")
    print(f"  α = {params_opt[0]:.3f} (time scaling)")
    print(f"  C₀ = {params_opt[1]:.3f} (gas complexity)")  
    print(f"  γ = {params_opt[2]:.3f} (gas exponent)")
    print(f"  δ = {params_opt[3]:.3f} (brightness exponent)")
    print(f"  Global χ²/N = {chi2_opt:.2f}")
    
    # Calculate final normalization with full sample
    from ledger_global_bandwidth import calculate_global_weights
    bandwidth_results = calculate_global_weights(master_table, params_opt)
    lambda_norm = bandwidth_results['lambda']
    
    print(f"\nGlobal normalization: λ = {lambda_norm:.3f}")
    print(f"Average boost: ρ = {1/lambda_norm:.3f}")
    
    # Analyze full sample
    results = analyze_full_sample(master_table, params_opt, lambda_norm)
    
    # Statistics
    chi2_values = [r['chi2_reduced'] for r in results]
    print(f"\nFull sample statistics ({len(results)} galaxies):")
    print(f"  Median χ²/N = {np.median(chi2_values):.2f}")
    print(f"  Mean χ²/N = {np.mean(chi2_values):.2f}")
    print(f"  Best fit: χ²/N = {np.min(chi2_values):.2f}")
    print(f"  Fraction with χ²/N < 5: {np.mean(np.array(chi2_values) < 5):.1%}")
    
    # Plot examples
    plot_example_fits(master_table, results, params_opt, lambda_norm)
    
    # Save everything
    output = {
        'params_opt': params_opt,
        'lambda_norm': lambda_norm,
        'bandwidth_results': bandwidth_results,
        'galaxy_results': results,
        'chi2_values': chi2_values
    }
    
    with open('ledger_unified_results.pkl', 'wb') as f:
        pickle.dump(output, f)
        
    print("\nSaved results to ledger_unified_results.pkl")

if __name__ == "__main__":
    main() 