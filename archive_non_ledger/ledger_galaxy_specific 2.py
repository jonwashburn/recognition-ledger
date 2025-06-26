#!/usr/bin/env python3
"""
Ledger solver with galaxy-specific radial profiles
Each galaxy gets its own spline profile with shared hyperparameters
"""

import numpy as np
import pickle
from scipy.optimize import differential_evolution, minimize
from scipy.interpolate import CubicSpline
import matplotlib.pyplot as plt

# Constants
G_kpc = 4.302e-6  # kpc (km/s)² / M_sun
tau_0 = 1e8  # years
Sigma_star = 1e8  # M_sun/kpc²

def create_galaxy_profile(r_data, params_profile, hyperparams):
    """
    Create galaxy-specific radial profile using cubic spline
    
    Control points at r = [0.5, 2, 8, 25] kpc
    params_profile = [n0, n1, n2, n3] values at control points
    hyperparams = [smoothness, prior_strength] for regularization
    """
    r_control = np.array([0.5, 2.0, 8.0, 25.0])  # kpc
    n_control = params_profile
    
    # Apply smoothness constraint
    smoothness = hyperparams[0]
    if smoothness > 0:
        # Smooth the control points towards a prior
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])  # Prior expectation
        n_control = (1 - smoothness) * n_control + smoothness * n_prior
    
    # Create spline (extrapolate flat beyond bounds)
    spline = CubicSpline(r_control, n_control, extrapolate=False)
    
    # Evaluate at data points
    n_r = np.zeros_like(r_data)
    mask_inner = r_data < r_control[0]
    mask_outer = r_data > r_control[-1]
    mask_mid = ~(mask_inner | mask_outer)
    
    n_r[mask_inner] = n_control[0]
    n_r[mask_outer] = n_control[-1]
    n_r[mask_mid] = spline(r_data[mask_mid])
    
    # Ensure positive values
    n_r = np.maximum(n_r, 0.5)
    
    return n_r

def recognition_weight_specific(r, galaxy_data, params_global, params_profile, hyperparams):
    """
    Recognition weight with galaxy-specific profile
    """
    alpha, C0, gamma, delta, h_z_ratio = params_global
    
    # Get galaxy properties
    T_dyn = galaxy_data['T_dyn']
    f_gas = galaxy_data['f_gas_true']
    Sigma_0 = galaxy_data['Sigma_0']
    R_d = galaxy_data['R_d']
    
    # Complexity factor
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Time factor
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Galaxy-specific radial profile
    n_r = create_galaxy_profile(r, params_profile, hyperparams)
    
    # Vertical correction
    h_z = h_z_ratio * R_d
    x = r / R_d
    f_profile = np.exp(-x/2) * (1 + x/3)
    zeta = 1 + 0.5 * (h_z / (r + 0.1*R_d)) * f_profile
    
    # Total weight
    w = xi * n_r * time_factor * zeta
    
    return w, n_r

def fit_galaxy_specific(galaxy_data, params_global, hyperparams, lambda_norm):
    """
    Fit galaxy with its own radial profile
    """
    r = galaxy_data['r']
    v_obs = galaxy_data['v_obs']
    df = galaxy_data['data']
    v_err = df['verr'].values
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bul = df['vbul'].values
    
    # Inner optimization: find best profile for this galaxy
    def objective_profile(params):
        params_profile = params[:4]  # n0, n1, n2, n3
        ml = params[4]  # M/L ratio
        
        # Get weights
        w, n_r = recognition_weight_specific(r, galaxy_data, params_global, 
                                            params_profile, hyperparams)
        G_eff = G_kpc * lambda_norm * w
        
        # Calculate model
        v_disk_scaled = v_disk * np.sqrt(ml)
        v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
        g_newton = v2_newton / r
        g_eff = g_newton * (G_eff / G_kpc)
        v_model = np.sqrt(g_eff * r)
        
        # Chi-squared
        chi2 = np.sum(((v_obs - v_model) / v_err)**2)
        
        # Regularization penalty
        prior_strength = hyperparams[1]
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        penalty = prior_strength * np.sum((params_profile - n_prior)**2)
        
        return chi2 + penalty
    
    # Initial guess and bounds
    x0 = [1.0, 3.0, 5.0, 8.0, 1.0]  # n0, n1, n2, n3, M/L
    bounds = [(0.5, 2.0), (1.0, 6.0), (2.0, 10.0), (3.0, 15.0), (0.1, 5.0)]
    
    # Optimize
    result = minimize(objective_profile, x0, bounds=bounds, method='L-BFGS-B')
    
    # Extract results
    params_profile = result.x[:4]
    ml_best = result.x[4]
    
    # Calculate final model
    w, n_r = recognition_weight_specific(r, galaxy_data, params_global, 
                                       params_profile, hyperparams)
    G_eff = G_kpc * lambda_norm * w
    
    v_disk_scaled = v_disk * np.sqrt(ml_best)
    v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
    g_newton = v2_newton / r
    g_eff = g_newton * (G_eff / G_kpc)
    v_model = np.sqrt(g_eff * r)
    
    chi2 = np.sum(((v_obs - v_model) / v_err)**2)
    
    return {
        'params_profile': params_profile,
        'ml': ml_best,
        'chi2': chi2,
        'chi2_reduced': chi2 / len(v_obs),
        'v_model': v_model,
        'n_r': n_r,
        'G_eff': G_eff
    }

def global_objective_specific(params, master_table):
    """
    Global objective with galaxy-specific profiles
    """
    # Split parameters
    params_global = params[:5]  # alpha, C0, gamma, delta, h_z_ratio
    hyperparams = params[5:]    # smoothness, prior_strength
    
    # First pass: fit all galaxies to get total weight
    all_profiles = []
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        
        # Use default profile for normalization calculation
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        w, _ = recognition_weight_specific(r, galaxy, params_global, 
                                         n_prior, hyperparams)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    lambda_norm = W_Newton / W_tot if W_tot > 0 else 1.0
    
    # Second pass: fit with galaxy-specific profiles
    total_chi2 = 0
    total_points = 0
    
    for name, galaxy in master_table.items():
        try:
            fit = fit_galaxy_specific(galaxy, params_global, hyperparams, lambda_norm)
            total_chi2 += fit['chi2']
            total_points += len(galaxy['v_obs'])
        except:
            continue
    
    return total_chi2 / total_points if total_points > 0 else 1e10

def optimize_specific(master_table, n_galaxies=30):
    """
    Optimize with galaxy-specific profiles
    """
    # Use subset for speed
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    # Bounds
    bounds = [
        (0.0, 1.0),    # alpha
        (0.0, 20.0),   # C0
        (0.5, 3.0),    # gamma
        (0.0, 1.0),    # delta
        (0.05, 0.5),   # h_z_ratio
        (0.0, 0.5),    # smoothness (0=free, 0.5=strongly regularized)
        (0.0, 10.0)    # prior_strength
    ]
    
    print(f"Optimizing with galaxy-specific profiles on {n_galaxies} galaxies...")
    print("This implements cubic spline profiles per galaxy")
    print("Expected improvement: χ²/N → 1.5-2.0")
    
    result = differential_evolution(
        lambda p: global_objective_specific(p, subset),
        bounds,
        maxiter=20,  # Fewer iterations as inner optimization is expensive
        popsize=10,
        disp=True
    )
    
    return result.x, result.fun

def analyze_specific_results(master_table, params_opt):
    """
    Analyze results with galaxy-specific profiles
    """
    # Split parameters
    params_global = params_opt[:5]
    hyperparams = params_opt[5:]
    
    print(f"\nGlobal parameters:")
    print(f"  α = {params_global[0]:.3f}")
    print(f"  C₀ = {params_global[1]:.3f}")
    print(f"  γ = {params_global[2]:.3f}")
    print(f"  δ = {params_global[3]:.3f}")
    print(f"  h_z/R_d = {params_global[4]:.3f}")
    print(f"\nHyperparameters:")
    print(f"  Smoothness = {hyperparams[0]:.3f}")
    print(f"  Prior strength = {hyperparams[1]:.3f}")
    
    # Calculate normalization
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        w, _ = recognition_weight_specific(r, galaxy, params_global, 
                                         n_prior, hyperparams)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    lambda_norm = W_Newton / W_tot
    print(f"\nGlobal normalization: λ = {lambda_norm:.3f}")
    
    # Fit all galaxies
    results = []
    print("\nFitting all galaxies with specific profiles...")
    
    for i, (name, galaxy) in enumerate(master_table.items()):
        if i % 20 == 0:
            print(f"  Progress: {i}/{len(master_table)}")
        
        try:
            fit = fit_galaxy_specific(galaxy, params_global, hyperparams, lambda_norm)
            fit['name'] = name
            fit['f_gas'] = galaxy['f_gas_true']
            results.append(fit)
        except:
            continue
    
    # Statistics
    chi2_values = [r['chi2_reduced'] for r in results]
    print(f"\nResults with galaxy-specific profiles:")
    print(f"  Median χ²/N = {np.median(chi2_values):.2f}")
    print(f"  Mean χ²/N = {np.mean(chi2_values):.2f}")
    print(f"  Fraction < 2: {np.mean(np.array(chi2_values) < 2):.1%}")
    print(f"  Fraction < 1.5: {np.mean(np.array(chi2_values) < 1.5):.1%}")
    print(f"  Fraction < 1.2: {np.mean(np.array(chi2_values) < 1.2):.1%}")
    
    # Plot examples showing profile diversity
    plot_specific_examples(master_table, results, params_global, hyperparams, lambda_norm)
    
    return results

def plot_specific_examples(master_table, results, params_global, hyperparams, lambda_norm):
    """
    Plot examples showing galaxy-specific profiles
    """
    # Sort by chi²
    results_sorted = sorted(results, key=lambda x: x['chi2_reduced'])
    
    # Pick best examples
    examples = results_sorted[:6]
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    for ax, res in zip(axes, examples):
        galaxy = master_table[res['name']]
        
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_err = galaxy['data']['verr'].values
        v_model = res['v_model']
        n_r = res['n_r']
        
        # Main plot: rotation curve
        ax.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=3,
                   alpha=0.6, label='Data')
        ax.plot(r, v_model, 'r-', linewidth=2,
               label=f'Model (M/L={res["ml"]:.1f})')
        
        # Add profile as secondary axis
        ax2 = ax.twinx()
        ax2.plot(r, n_r, 'b--', linewidth=1.5, alpha=0.7)
        ax2.set_ylabel('n(r) [refresh interval]', color='b')
        ax2.tick_params(axis='y', labelcolor='b')
        ax2.set_ylim(0, 15)
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{res["name"]}: χ²/N={res["chi2_reduced"]:.2f}')
        ax.legend(loc='upper right')
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('ledger_galaxy_specific_examples.png', dpi=150)
    print("Saved: ledger_galaxy_specific_examples.png")

def main():
    """Main execution"""
    
    # Load master table
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize
    params_opt, chi2_opt = optimize_specific(master_table, n_galaxies=30)
    
    print("\n" + "="*60)
    print("OPTIMIZATION COMPLETE")
    print(f"Global χ²/N = {chi2_opt:.2f}")
    print("="*60)
    
    # Analyze full sample
    results = analyze_specific_results(master_table, params_opt)
    
    # Save results
    output = {
        'params_opt': params_opt,
        'results': results,
        'chi2_opt': chi2_opt
    }
    
    with open('ledger_specific_results.pkl', 'wb') as f:
        pickle.dump(output, f)
    
    print("\nSaved: ledger_specific_results.pkl")

if __name__ == "__main__":
    main() 