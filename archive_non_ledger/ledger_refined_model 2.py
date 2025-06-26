import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import differential_evolution
from scipy.interpolate import CubicSpline
import pickle
import pandas as pd

def load_master_table():
    """Load the master galaxy table with all parameters"""
    with open('sparc_master.pkl', 'rb') as f:
        return pickle.load(f)

def recognition_weight_refined(r, params, galaxy):
    """
    Refined recognition weight function with simple corrections
    
    w(r) = λ × ξ × n(r) × (T_dyn/τ_0)^α × ζ(r) × B(r)
    
    where B(r) is a simple central boost for bars/bulges
    """
    alpha, C0, gamma, delta, h_z_ratio = params[:5]
    f_central = params[5]  # Central boost factor
    r_central = params[6]  # Central boost scale
    n_values = params[7:11]  # Spline control points for n(r)
    
    # Create spline for n(r)
    r_knots = np.array([0.5, 2.0, 8.0, 25.0])
    n_spline = CubicSpline(r_knots, n_values, bc_type='natural', extrapolate=True)
    n_r = np.maximum(n_spline(r), 0.1)  # Keep positive
    
    # Dynamical time factor
    v_circ = galaxy['v_baryon']
    v_circ = np.maximum(v_circ, 10.0)
    T_dyn = 2 * np.pi * r / (v_circ * 3.086e13)  # Convert to seconds
    tau_0 = 14e9 * 365.25 * 24 * 3600  # 14 Gyr in seconds
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Basic complexity factor
    f_gas = galaxy.get('f_gas_true', 0.1)
    Sigma_0 = galaxy.get('Sigma_0', 1e8)
    Sigma_star = 1e8  # M_sun/kpc^2
    xi = 1 + C0 * f_gas**gamma * (Sigma_0/Sigma_star)**delta
    
    # Geometric correction for disk thickness
    R_d = galaxy.get('R_d', 2.0)
    h_z = h_z_ratio * R_d
    f_thick = (1 - np.exp(-r/R_d)) / (r/R_d + 1e-10)
    zeta_r = 1 + 0.5 * (h_z/r) * f_thick
    
    # Simple central boost for bars/bulges
    # Exponential decay from center
    B_r = 1 + f_central * np.exp(-r/r_central)
    
    # Total weight
    w = n_r * time_factor * xi * zeta_r * B_r
    
    return w

def calculate_chi2_refined(params_global, galaxies, lambda_norm=0.119, verbose=False):
    """Calculate chi-squared with refined model"""
    alpha, C0, gamma, delta, h_z_ratio, f_central, r_central = params_global[:7]
    smooth_scale = params_global[7]
    prior_strength = params_global[8]
    
    total_chi2 = 0
    total_N = 0
    
    for gname, galaxy in galaxies.items():
        # Get data
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_bar = galaxy['v_baryon']
        
        # Estimate errors (typical for SPARC)
        v_err = np.maximum(0.03 * v_obs, 3.0)  # 3% error or 3 km/s minimum
        
        # Skip if too few points
        if len(r) < 5:
            continue
            
        # Galaxy-specific n(r) parameters
        n_params = np.array([2.0, 5.0, 10.0, 2.0])  # Default profile
        
        # Calculate recognition weight
        params = np.concatenate([[alpha, C0, gamma, delta, h_z_ratio, f_central, r_central], n_params])
        w = recognition_weight_refined(r, params, galaxy)
        
        # Global normalization for bandwidth conservation
        w = lambda_norm * w
        
        # Calculate model velocity
        v_model = np.sqrt(w * v_bar**2)
        
        # Simple error model with 10% systematic error
        sigma_tot = np.sqrt(v_err**2 + (0.1 * v_model)**2)
        sigma_tot = np.maximum(sigma_tot, 3.0)  # Minimum 3 km/s
        
        # Chi-squared
        chi2 = np.sum(((v_obs - v_model) / sigma_tot)**2)
        
        # Add smoothness prior on n(r)
        if smooth_scale > 0:
            dn = np.diff(n_params)
            chi2 += smooth_scale * np.sum(dn**2)
        
        # Add prior to keep parameters reasonable
        if prior_strength > 0:
            chi2 += prior_strength * np.sum((n_params - 5.0)**2 / 25.0)
        
        total_chi2 += chi2
        total_N += len(r)
    
    return total_chi2 / total_N

def optimize_refined_model(galaxies, n_galaxies=40):
    """Optimize the refined model"""
    
    # Select subset for optimization
    galaxy_names = list(galaxies.keys())[:n_galaxies]
    subset = {name: galaxies[name] for name in galaxy_names}
    
    print(f"Optimizing refined model on {len(subset)} galaxies...")
    
    # First, find optimal lambda normalization using grid search
    print("Finding optimal λ normalization...")
    lambda_values = np.logspace(np.log10(0.05), np.log10(0.5), 20)
    best_lambda = 0.119
    best_chi2 = float('inf')
    
    # Use reasonable default parameters for lambda search
    default_params = [0.194, 5.064, 2.953, 0.216, 0.25, 0.5, 1.0, 0.003, 0.032]
    
    for lam in lambda_values:
        chi2 = calculate_chi2_refined(default_params, subset, lambda_norm=lam)
        if chi2 < best_chi2:
            best_chi2 = chi2
            best_lambda = lam
    
    print(f"Optimal λ = {best_lambda:.3f}")
    
    # Now optimize other parameters with fixed lambda
    print("Optimizing model parameters...")
    
    # Parameter bounds
    # [alpha, C0, gamma, delta, h_z_ratio, f_central, r_central, smooth, prior]
    bounds = [
        (0.1, 0.5),      # alpha: time scaling
        (1.0, 10.0),     # C0: complexity amplitude  
        (1.0, 4.0),      # gamma: gas power
        (0.1, 1.0),      # delta: surface brightness power
        (0.1, 0.5),      # h_z/R_d: disk thickness
        (0.0, 2.0),      # f_central: central boost amplitude
        (0.5, 3.0),      # r_central: central boost scale (kpc)
        (0.0, 0.01),     # smoothness scale
        (0.0, 0.1),      # prior strength
    ]
    
    # Create objective function
    def objective(p):
        return calculate_chi2_refined(p, subset, lambda_norm=best_lambda, verbose=False)
    
    # Optimize
    result = differential_evolution(
        objective,
        bounds,
        seed=42,
        maxiter=200,
        popsize=15,
        tol=1e-4,
        workers=1,
        updating='deferred',
        disp=True
    )
    
    print("\n" + "="*60)
    print("REFINED MODEL OPTIMIZATION COMPLETE")
    print(f"Global χ²/N = {result.fun:.2f}")
    print("="*60)
    
    # Extract parameters
    params = result.x
    print("\nOptimized parameters:")
    print(f"  α = {params[0]:.3f}")
    print(f"  C₀ = {params[1]:.3f}")
    print(f"  γ = {params[2]:.3f}")
    print(f"  δ = {params[3]:.3f}")
    print(f"  h_z/R_d = {params[4]:.3f}")
    print(f"  f_central = {params[5]:.3f}")
    print(f"  r_central = {params[6]:.3f} kpc")
    print(f"  Smoothness = {params[7]:.3f}")
    print(f"  Prior strength = {params[8]:.3f}")
    print(f"Global normalization: λ = {best_lambda:.3f}")
    
    return params, best_lambda

def fit_all_galaxies_refined(galaxies, params_global, lambda_norm):
    """Fit all galaxies with refined model"""
    print("\nFitting all galaxies with refined model...")
    
    results = {}
    
    for i, (gname, galaxy) in enumerate(galaxies.items()):
        if i % 25 == 0:
            print(f"  Progress: {i}/{len(galaxies)}")
            
        # Get data
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_bar = galaxy['v_baryon']
        
        # Estimate errors
        v_err = np.maximum(0.03 * v_obs, 3.0)
        
        if len(r) < 5:
            continue
        
        # Optimize galaxy-specific n(r)
        def chi2_galaxy(n_params):
            params = np.concatenate([params_global[:7], n_params])
            w = recognition_weight_refined(r, params, galaxy)
            w = lambda_norm * w
            v_model = np.sqrt(w * v_bar**2)
            
            # Error model
            sigma_tot = np.sqrt(v_err**2 + (0.1 * v_model)**2)
            sigma_tot = np.maximum(sigma_tot, 3.0)
            
            chi2 = np.sum(((v_obs - v_model) / sigma_tot)**2)
            
            # Smoothness prior
            if params_global[7] > 0:
                dn = np.diff(n_params)
                chi2 += params_global[7] * np.sum(dn**2) * len(r)
                
            return chi2
        
        # Optimize n(r) for this galaxy
        n_bounds = [(0.1, 100.0)] * 4
        res = differential_evolution(chi2_galaxy, n_bounds, seed=42, maxiter=50, 
                                   popsize=10, tol=0.01, disp=False)
        
        n_opt = res.x
        chi2_N = res.fun / len(r)
        
        # Store results
        results[gname] = {
            'chi2_N': chi2_N,
            'n_params': n_opt,
            'N_points': len(r),
            'M_star': galaxy.get('M_star_est', 1e9)
        }
    
    # Calculate statistics
    chi2_N_values = [r['chi2_N'] for r in results.values()]
    chi2_N_values = np.array(chi2_N_values)
    
    print("\nResults with refined model:")
    print(f"  Overall median χ²/N = {np.median(chi2_N_values):.2f}")
    print(f"  Overall mean χ²/N = {np.mean(chi2_N_values):.2f}")
    
    # By galaxy type
    dwarf_chi2 = []
    spiral_chi2 = []
    
    for gname, result in results.items():
        if result['M_star'] < 1e9:
            dwarf_chi2.append(result['chi2_N'])
        else:
            spiral_chi2.append(result['chi2_N'])
    
    if dwarf_chi2:
        print(f"  Dwarf median χ²/N = {np.median(dwarf_chi2):.2f}")
    if spiral_chi2:
        print(f"  Spiral median χ²/N = {np.median(spiral_chi2):.2f}")
        
    print(f"  Fraction < 1.5: {100*np.sum(chi2_N_values < 1.5)/len(chi2_N_values):.1f}%")
    print(f"  Fraction < 1.2: {100*np.sum(chi2_N_values < 1.2)/len(chi2_N_values):.1f}%")
    print(f"  Fraction < 1.0: {100*np.sum(chi2_N_values < 1.0)/len(chi2_N_values):.1f}%")
    print(f"  Fraction < 0.5: {100*np.sum(chi2_N_values < 0.5)/len(chi2_N_values):.1f}%")
    print(f"  Fraction < 0.3: {100*np.sum(chi2_N_values < 0.3)/len(chi2_N_values):.1f}%")
    
    return results

def plot_refined_examples(galaxies, results, params_global, lambda_norm):
    """Plot example fits with refined model"""
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    # Select examples - mix of good and challenging fits
    example_names = ['DDO154', 'NGC2403', 'NGC3198', 'NGC6503', 'UGC2885', 'F568-3']
    
    for idx, gname in enumerate(example_names):
        if gname not in galaxies or gname not in results:
            continue
            
        ax = axes[idx]
        galaxy = galaxies[gname]
        result = results[gname]
        
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        v_err = np.maximum(0.03 * v_obs, 3.0)
        v_bar = galaxy['v_baryon']
        
        # Calculate model with refined weight
        params = np.concatenate([params_global[:7], result['n_params']])
        w = recognition_weight_refined(r, params, galaxy)
        w = lambda_norm * w
        v_model = np.sqrt(w * v_bar**2)
        
        # Plot
        ax.errorbar(r, v_obs, yerr=v_err, fmt='o', color='black', 
                   markersize=3, alpha=0.6, label='Observed')
        ax.plot(r, v_bar, '--', color='blue', alpha=0.7, label='Baryonic')
        ax.plot(r, v_model, '-', color='red', linewidth=2, label='LNAL Refined')
        
        ax.set_xlabel('Radius (kpc)')
        ax.set_ylabel('Velocity (km/s)')
        ax.set_title(f'{gname} (χ²/N = {result["chi2_N"]:.2f})')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='lower right', fontsize=8)
        ax.set_xlim(0, None)
        ax.set_ylim(0, None)
    
    plt.tight_layout()
    plt.savefig('ledger_refined_examples.png', dpi=150, bbox_inches='tight')
    print("\nSaved: ledger_refined_examples.png")

if __name__ == "__main__":
    # Load data
    print("Loading master table...")
    master_table = load_master_table()
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize refined model
    params_global, lambda_norm = optimize_refined_model(master_table, n_galaxies=40)
    
    # Fit all galaxies
    results = fit_all_galaxies_refined(master_table, params_global, lambda_norm)
    
    # Create plots
    plot_refined_examples(master_table, results, params_global, lambda_norm)
    
    # Save results
    with open('ledger_refined_results.pkl', 'wb') as f:
        pickle.dump({
            'params_global': params_global,
            'lambda_norm': lambda_norm,
            'results': results,
            'median_chi2_N': np.median([r['chi2_N'] for r in results.values()])
        }, f)
    print("Saved: ledger_refined_results.pkl") 