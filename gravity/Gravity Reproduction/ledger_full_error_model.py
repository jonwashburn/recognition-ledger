#!/usr/bin/env python3
"""
Ledger solver with full error model (Step 6)
Includes:
- Observational errors
- Beam smearing effects  
- Asymmetric drift correction
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

# Beam size for SPARC
BEAM_ARCSEC = 15.0  # arcseconds

def compute_full_error(v_err, r, v_obs, distance, galaxy_type, error_params):
    """
    Compute full error including:
    - Observational error (v_err)
    - Beam smearing  
    - Asymmetric drift
    
    error_params = [alpha_beam, beta_asym]
    """
    alpha_beam, beta_asym = error_params
    
    # Convert beam size to kpc
    beam_kpc = BEAM_ARCSEC * distance / 206265.0  # arcsec to radians to kpc
    
    # Beam smearing error
    # Larger near center where velocity gradient is steep
    dr = np.gradient(r)
    dr = np.where(dr > 0, dr, 0.1)  # Avoid division by zero
    sigma_beam = alpha_beam * beam_kpc * v_obs / (r + beam_kpc)
    
    # Asymmetric drift correction (mainly for dwarfs)
    # Stronger for gas-poor, pressure-supported systems
    if galaxy_type == 'dwarf':
        sigma_asym = beta_asym * v_obs * 0.1  # 10% effect for dwarfs
    else:
        sigma_asym = beta_asym * v_obs * 0.02  # 2% for spirals
    
    # Total error
    sigma_total = np.sqrt(v_err**2 + sigma_beam**2 + sigma_asym**2)
    
    return sigma_total

def create_galaxy_profile(r_data, params_profile, hyperparams):
    """Galaxy-specific radial profile using cubic spline"""
    r_control = np.array([0.5, 2.0, 8.0, 25.0])  # kpc
    n_control = params_profile
    
    # Apply smoothness
    smoothness = hyperparams[0]
    if smoothness > 0:
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        n_control = (1 - smoothness) * n_control + smoothness * n_prior
    
    # Create spline
    spline = CubicSpline(r_control, n_control, extrapolate=False)
    
    # Evaluate
    n_r = np.zeros_like(r_data)
    mask_inner = r_data < r_control[0]
    mask_outer = r_data > r_control[-1]
    mask_mid = ~(mask_inner | mask_outer)
    
    n_r[mask_inner] = n_control[0]
    n_r[mask_outer] = n_control[-1]
    n_r[mask_mid] = spline(r_data[mask_mid])
    
    n_r = np.maximum(n_r, 0.5)
    
    return n_r

def recognition_weight_full_error(r, galaxy_data, params_global, params_profile, hyperparams):
    """Recognition weight with vertical correction"""
    alpha, C0, gamma, delta, h_z_ratio = params_global[:5]
    
    # Galaxy properties
    T_dyn = galaxy_data['T_dyn']
    f_gas = galaxy_data['f_gas_true']
    Sigma_0 = galaxy_data['Sigma_0']
    R_d = galaxy_data['R_d']
    
    # Complexity factor
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Time factor
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Galaxy-specific profile
    n_r = create_galaxy_profile(r, params_profile, hyperparams)
    
    # Vertical correction
    h_z = h_z_ratio * R_d
    x = r / R_d
    f_profile = np.exp(-x/2) * (1 + x/3)
    zeta = 1 + 0.5 * (h_z / (r + 0.1*R_d)) * f_profile
    
    # Total weight
    w = xi * n_r * time_factor * zeta
    
    return w, n_r

def fit_galaxy_full_error(galaxy_data, params_global, hyperparams, error_params, lambda_norm):
    """Fit galaxy with full error model"""
    r = galaxy_data['r']
    v_obs = galaxy_data['v_obs']
    df = galaxy_data['data']
    v_err_base = df['verr'].values
    v_gas = df['vgas'].values
    v_disk = df['vdisk'].values
    v_bul = df['vbul'].values
    
    # Determine galaxy type
    v_max = np.max(v_obs)
    galaxy_type = 'dwarf' if v_max < 80 else 'spiral'
    
    # Get distance (default 10 Mpc if not available)
    distance = galaxy_data.get('distance', 10.0)
    
    # Inner optimization
    def objective_profile(params):
        params_profile = params[:4]
        ml = params[4]
        
        # Get weights
        w, n_r = recognition_weight_full_error(r, galaxy_data, params_global, 
                                              params_profile, hyperparams)
        G_eff = G_kpc * lambda_norm * w
        
        # Calculate model
        v_disk_scaled = v_disk * np.sqrt(ml)
        v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
        g_newton = v2_newton / r
        g_eff = g_newton * (G_eff / G_kpc)
        v_model = np.sqrt(g_eff * r)
        
        # Full error
        sigma_total = compute_full_error(v_err_base, r, v_obs, distance, 
                                       galaxy_type, error_params)
        
        # Chi-squared with full error
        chi2 = np.sum(((v_obs - v_model) / sigma_total)**2)
        
        # Regularization
        prior_strength = hyperparams[1]
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        penalty = prior_strength * np.sum((params_profile - n_prior)**2)
        
        return chi2 + penalty
    
    # Initial guess
    x0 = [1.0, 3.0, 5.0, 8.0, 1.0]
    bounds = [(0.5, 2.0), (1.0, 6.0), (2.0, 10.0), (3.0, 15.0), (0.1, 5.0)]
    
    # Optimize
    result = minimize(objective_profile, x0, bounds=bounds, method='L-BFGS-B')
    
    # Extract results
    params_profile = result.x[:4]
    ml_best = result.x[4]
    
    # Final calculation
    w, n_r = recognition_weight_full_error(r, galaxy_data, params_global, 
                                         params_profile, hyperparams)
    G_eff = G_kpc * lambda_norm * w
    
    v_disk_scaled = v_disk * np.sqrt(ml_best)
    v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
    g_newton = v2_newton / r
    g_eff = g_newton * (G_eff / G_kpc)
    v_model = np.sqrt(g_eff * r)
    
    # Final error
    sigma_total = compute_full_error(v_err_base, r, v_obs, distance, 
                                   galaxy_type, error_params)
    
    chi2 = np.sum(((v_obs - v_model) / sigma_total)**2)
    
    return {
        'params_profile': params_profile,
        'ml': ml_best,
        'chi2': chi2,
        'chi2_reduced': chi2 / len(v_obs),
        'v_model': v_model,
        'n_r': n_r,
        'sigma_total': sigma_total,
        'galaxy_type': galaxy_type
    }

def global_objective_full_error(params, master_table):
    """Global objective with full error model"""
    # Split parameters
    params_global = params[:5]
    hyperparams = params[5:7]
    error_params = params[7:9]
    
    # Calculate normalization
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        w, _ = recognition_weight_full_error(r, galaxy, params_global, 
                                           n_prior, hyperparams)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    lambda_norm = W_Newton / W_tot if W_tot > 0 else 1.0
    
    # Fit all galaxies
    total_chi2 = 0
    total_points = 0
    
    for name, galaxy in master_table.items():
        try:
            fit = fit_galaxy_full_error(galaxy, params_global, hyperparams, 
                                      error_params, lambda_norm)
            total_chi2 += fit['chi2']
            total_points += len(galaxy['v_obs'])
        except:
            continue
    
    return total_chi2 / total_points if total_points > 0 else 1e10

def optimize_full_error(master_table, n_galaxies=40):
    """Optimize with full error model"""
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    bounds = [
        # Global parameters
        (0.0, 1.0),    # alpha
        (0.0, 15.0),   # C0
        (0.5, 3.0),    # gamma
        (0.0, 1.0),    # delta
        (0.05, 0.5),   # h_z_ratio
        # Hyperparameters
        (0.0, 0.3),    # smoothness
        (0.0, 5.0),    # prior_strength
        # Error parameters
        (0.0, 1.0),    # alpha_beam
        (0.0, 0.5)     # beta_asym
    ]
    
    print(f"Optimizing with full error model on {n_galaxies} galaxies...")
    print("Including beam smearing and asymmetric drift")
    
    result = differential_evolution(
        lambda p: global_objective_full_error(p, subset),
        bounds,
        maxiter=25,
        popsize=12,
        disp=True
    )
    
    return result.x, result.fun

def analyze_full_error_results(master_table, params_opt):
    """Analyze results with full error model"""
    params_global = params_opt[:5]
    hyperparams = params_opt[5:7]
    error_params = params_opt[7:9]
    
    print(f"\nOptimized parameters:")
    print(f"  α = {params_global[0]:.3f}")
    print(f"  C₀ = {params_global[1]:.3f}")
    print(f"  γ = {params_global[2]:.3f}")
    print(f"  δ = {params_global[3]:.3f}")
    print(f"  h_z/R_d = {params_global[4]:.3f}")
    print(f"  Smoothness = {hyperparams[0]:.3f}")
    print(f"  Prior strength = {hyperparams[1]:.3f}")
    print(f"  α_beam = {error_params[0]:.3f}")
    print(f"  β_asym = {error_params[1]:.3f}")
    
    # Calculate normalization
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        n_prior = np.array([1.0, 3.0, 5.0, 8.0])
        w, _ = recognition_weight_full_error(r, galaxy, params_global, 
                                           n_prior, hyperparams)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
    
    lambda_norm = W_Newton / W_tot
    print(f"\nGlobal normalization: λ = {lambda_norm:.3f}")
    
    # Fit all galaxies
    results = []
    dwarf_chi2 = []
    spiral_chi2 = []
    
    print("\nFitting all galaxies with full error model...")
    
    for i, (name, galaxy) in enumerate(master_table.items()):
        if i % 25 == 0:
            print(f"  Progress: {i}/{len(master_table)}")
        
        try:
            fit = fit_galaxy_full_error(galaxy, params_global, hyperparams, 
                                      error_params, lambda_norm)
            fit['name'] = name
            results.append(fit)
            
            if fit['galaxy_type'] == 'dwarf':
                dwarf_chi2.append(fit['chi2_reduced'])
            else:
                spiral_chi2.append(fit['chi2_reduced'])
        except:
            continue
    
    # Statistics
    all_chi2 = [r['chi2_reduced'] for r in results]
    print(f"\nResults with full error model:")
    print(f"  Overall median χ²/N = {np.median(all_chi2):.2f}")
    print(f"  Overall mean χ²/N = {np.mean(all_chi2):.2f}")
    
    if dwarf_chi2:
        print(f"  Dwarf median χ²/N = {np.median(dwarf_chi2):.2f}")
    if spiral_chi2:
        print(f"  Spiral median χ²/N = {np.median(spiral_chi2):.2f}")
    
    print(f"  Fraction < 1.5: {np.mean(np.array(all_chi2) < 1.5):.1%}")
    print(f"  Fraction < 1.2: {np.mean(np.array(all_chi2) < 1.2):.1%}")
    print(f"  Fraction < 1.0: {np.mean(np.array(all_chi2) < 1.0):.1%}")
    
    # Plot examples
    plot_full_error_examples(master_table, results, params_global, 
                           hyperparams, error_params, lambda_norm)
    
    return results

def plot_full_error_examples(master_table, results, params_global, 
                            hyperparams, error_params, lambda_norm):
    """Plot examples showing error model effects"""
    results_sorted = sorted(results, key=lambda x: x['chi2_reduced'])
    
    # Get mix of types
    examples = []
    for galaxy_type in ['dwarf', 'spiral']:
        type_results = [r for r in results_sorted if r['galaxy_type'] == galaxy_type]
        if type_results:
            examples.extend(type_results[:3])
    
    examples = examples[:6]
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    for ax, res in zip(axes, examples):
        galaxy = master_table[res['name']]
        
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_err_base = galaxy['data']['verr'].values
        v_model = res['v_model']
        sigma_total = res['sigma_total']
        
        # Plot with both error bars
        ax.errorbar(r, v_obs, yerr=v_err_base, fmt='ko', markersize=3,
                   alpha=0.4, label='Base errors')
        ax.errorbar(r, v_obs, yerr=sigma_total, fmt='ko', markersize=3,
                   alpha=0.8, label='Full errors')
        ax.plot(r, v_model, 'r-', linewidth=2,
               label=f'Model (M/L={res["ml"]:.1f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{res["name"]} ({res["galaxy_type"]}): χ²/N={res["chi2_reduced"]:.2f}')
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('ledger_full_error_examples.png', dpi=150)
    print("Saved: ledger_full_error_examples.png")

def main():
    """Main execution"""
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize
    params_opt, chi2_opt = optimize_full_error(master_table, n_galaxies=40)
    
    print("\n" + "="*60)
    print("OPTIMIZATION WITH FULL ERROR MODEL COMPLETE")
    print(f"Global χ²/N = {chi2_opt:.2f}")
    print("="*60)
    
    # Analyze
    results = analyze_full_error_results(master_table, params_opt)
    
    # Save
    output = {
        'params_opt': params_opt,
        'results': results,
        'chi2_opt': chi2_opt
    }
    
    with open('ledger_full_error_results.pkl', 'wb') as f:
        pickle.dump(output, f)
    
    print("\nSaved: ledger_full_error_results.pkl")

if __name__ == "__main__":
    main() 