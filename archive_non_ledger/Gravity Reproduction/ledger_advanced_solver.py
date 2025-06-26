#!/usr/bin/env python3
"""
Advanced ledger-refresh solver with:
- Radial-dependent recognition weight
- Surface brightness effects
- Global bandwidth normalization
- Machine learning inspired features
"""

import numpy as np
import pickle
from scipy.optimize import minimize, differential_evolution
from scipy.interpolate import interp1d
import matplotlib.pyplot as plt

# Constants
G_kpc = 4.302e-6  # kpc (km/s)² / M_sun
tau_0 = 1e8  # years  
Sigma_star = 1e8  # M_sun/kpc²
r_star = 10.0  # kpc

def advanced_recognition_weight(r, T_dyn, f_gas, Sigma_0, R_d, params):
    """
    Advanced recognition weight with radial dependence
    
    w(r) = λ × ξ × n(r)
    
    where:
    - ξ = complexity factor (gas, surface brightness)
    - n(r) = radial-dependent refresh interval
    - λ = global normalization
    """
    alpha, beta, C0, gamma, delta, r1, n1, n2 = params[:8]
    
    # Complexity factor (galaxy properties)
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Radial profile with smooth transitions
    # Inner region: fast updates (n ≈ 1)
    # Disk region: moderate updates (n ≈ n1)  
    # Outer region: slow updates (n ≈ n2)
    
    # Smooth transition function
    x1 = (r / r1) ** beta
    trans1 = 1 / (1 + x1)
    trans2 = x1 / (1 + x1)
    
    # Base refresh interval
    n_base = trans1 * 1.0 + trans2 * n1
    
    # Add outer transition
    if len(params) > 8:
        r2 = params[8]
        x2 = (r / r2) ** beta
        trans3 = x2 / (1 + x2)
        n_base = (1 - trans3) * n_base + trans3 * n2
    else:
        # Simple outer boost
        outer_mask = r > 3 * r1
        n_base = np.where(outer_mask, n2, n_base)
    
    # Time-based modulation
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Total weight (before normalization)
    w = xi * n_base * time_factor
    
    return w

def calculate_bandwidth_norm(master_table, params):
    """Calculate normalization to satisfy bandwidth constraint"""
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        
        # Get weights
        w = advanced_recognition_weight(
            r, galaxy['T_dyn'], galaxy['f_gas_true'], 
            galaxy['Sigma_0'], galaxy['R_d'], params
        )
        
        # Integrate
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    # Normalization factor
    return W_Newton / W_tot if W_tot > 0 else 1.0

def fit_galaxy_ml(galaxy_data, params, lambda_norm):
    """Fit stellar M/L for a single galaxy"""
    r = galaxy_data['r']
    v_obs = galaxy_data['v_obs']
    df = galaxy_data['data']
    v_err = df['verr'].values
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bul = df['vbul'].values
    
    # Get normalized weights
    w = advanced_recognition_weight(
        r, galaxy_data['T_dyn'], galaxy_data['f_gas_true'],
        galaxy_data['Sigma_0'], galaxy_data['R_d'], params
    )
    
    # Effective G
    G_eff = G_kpc * lambda_norm * w
    
    # Find best M/L
    ml_values = np.linspace(0.1, 5.0, 50)
    chi2_values = []
    
    for ml in ml_values:
        v_disk_scaled = v_disk * np.sqrt(ml)
        v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
        g_newton = v2_newton / r
        g_eff = g_newton * (G_eff / G_kpc)
        v_model = np.sqrt(g_eff * r)
        
        chi2 = np.sum(((v_obs - v_model) / v_err)**2)
        chi2_values.append(chi2)
    
    # Best M/L
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
        'G_eff': G_eff
    }

def global_objective(params, master_table):
    """Global chi² with bandwidth constraint"""
    # Calculate normalization
    lambda_norm = calculate_bandwidth_norm(master_table, params)
    
    # Fit all galaxies
    total_chi2 = 0
    total_points = 0
    
    for name, galaxy in master_table.items():
        try:
            fit = fit_galaxy_ml(galaxy, params, lambda_norm)
            total_chi2 += fit['chi2']
            total_points += len(galaxy['v_obs'])
        except:
            continue
    
    global_chi2 = total_chi2 / total_points if total_points > 0 else 1e10
    
    # Penalty for extreme parameters
    penalty = 0
    if params[6] > 20:  # n2 too large
        penalty += (params[6] - 20)**2
        
    return global_chi2 + penalty

def optimize_advanced_parameters(master_table, n_galaxies=50):
    """Optimize using differential evolution"""
    
    # Use subset for speed
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    # Parameter bounds
    bounds = [
        (0.0, 1.0),    # alpha: time scaling
        (1.0, 3.0),    # beta: radial transition sharpness
        (0.0, 20.0),   # C0: gas complexity
        (0.5, 3.0),    # gamma: gas exponent
        (0.0, 1.0),    # delta: surface brightness exponent
        (0.5, 5.0),    # r1: inner transition radius (kpc)
        (1.0, 5.0),    # n1: disk boost factor
        (2.0, 20.0),   # n2: outer boost factor
        (10.0, 50.0)   # r2: outer transition radius (kpc)
    ]
    
    print(f"Optimizing {len(bounds)} parameters on {n_galaxies} galaxies...")
    print("This may take several minutes...")
    
    result = differential_evolution(
        lambda p: global_objective(p, subset),
        bounds,
        maxiter=30,
        popsize=15,
        disp=True
    )
    
    return result.x, result.fun

def analyze_and_plot(master_table, params_opt, output_prefix='ledger_advanced'):
    """Full analysis with optimized parameters"""
    
    # Calculate final normalization
    lambda_norm = calculate_bandwidth_norm(master_table, params_opt)
    
    print(f"\nFinal normalization: λ = {lambda_norm:.3f}")
    print(f"Average boost: ρ = {1/lambda_norm:.3f}")
    
    # Fit all galaxies
    results = []
    print("\nFitting all galaxies...")
    
    for i, (name, galaxy) in enumerate(master_table.items()):
        if i % 30 == 0:
            print(f"  Progress: {i}/{len(master_table)}")
            
        try:
            fit = fit_galaxy_ml(galaxy, params_opt, lambda_norm)
            fit['name'] = name
            fit['f_gas'] = galaxy['f_gas_true']
            results.append(fit)
        except:
            continue
    
    # Statistics
    chi2_values = [r['chi2_reduced'] for r in results]
    chi2_median = np.median(chi2_values)
    chi2_mean = np.mean(chi2_values)
    frac_good = np.mean(np.array(chi2_values) < 3)
    
    print(f"\nFinal statistics ({len(results)} galaxies):")
    print(f"  Median χ²/N = {chi2_median:.2f}")
    print(f"  Mean χ²/N = {chi2_mean:.2f}")
    print(f"  Fraction with χ²/N < 3: {frac_good:.1%}")
    
    # Plot best examples
    results_sorted = sorted(results, key=lambda x: x['chi2_reduced'])
    n_examples = min(6, len(results))
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    for i, ax in enumerate(axes[:n_examples]):
        res = results_sorted[i]
        galaxy = master_table[res['name']]
        
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_err = galaxy['data']['verr'].values
        v_model = res['v_model']
        
        ax.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=3,
                   alpha=0.6, label='Data')
        ax.plot(r, v_model, 'r-', linewidth=2,
               label=f'Model (M/L={res["ml"]:.1f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{res["name"]}: χ²/N={res["chi2_reduced"]:.2f}, '
                    f'f_gas={res["f_gas"]:.2f}')
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(f'{output_prefix}_best_fits.png', dpi=150)
    print(f"Saved: {output_prefix}_best_fits.png")
    
    # Save results
    output = {
        'params_opt': params_opt,
        'lambda_norm': lambda_norm,
        'results': results,
        'statistics': {
            'median_chi2': chi2_median,
            'mean_chi2': chi2_mean,
            'frac_good': frac_good
        }
    }
    
    with open(f'{output_prefix}_results.pkl', 'wb') as f:
        pickle.dump(output, f)
        
    print(f"Saved: {output_prefix}_results.pkl")
    
    return results

def main():
    """Main execution"""
    
    # Load master table
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize
    params_opt, chi2_opt = optimize_advanced_parameters(master_table, n_galaxies=50)
    
    print("\n" + "="*60)
    print("OPTIMIZED PARAMETERS:")
    print("="*60)
    param_names = ['α', 'β', 'C₀', 'γ', 'δ', 'r₁', 'n₁', 'n₂', 'r₂']
    for i, (name, val) in enumerate(zip(param_names[:len(params_opt)], params_opt)):
        print(f"  {name} = {val:.3f}")
    print(f"\nOptimization χ²/N = {chi2_opt:.2f}")
    print("="*60)
    
    # Analyze
    results = analyze_and_plot(master_table, params_opt)
    
    print("\nDone!")

if __name__ == "__main__":
    main() 