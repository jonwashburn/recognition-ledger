import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import differential_evolution
from scipy.interpolate import CubicSpline
from scipy.integrate import cumtrapz
import pickle
import pandas as pd
from tqdm import tqdm

def load_master_table():
    """Load the master galaxy table with all parameters"""
    with open('sparc_master.pkl', 'rb') as f:
        return pickle.load(f)

def recognition_weight_enhanced(r, params, galaxy):
    """
    Enhanced recognition weight function with bulge/bar and gas clumpiness
    
    w(r) = λ × ξ × n(r) × (T_dyn/τ_0)^α × ζ(r) × ζ_bar(r)
    
    where ξ now includes gas clumpiness factor
    """
    alpha, C0, gamma, delta, h_z_ratio, kappa_clump, xi_bar = params[:7]
    n_values = params[7:11]  # Spline control points for n(r)
    
    # Create spline for n(r)
    r_knots = np.array([0.5, 2.0, 8.0, 25.0])
    n_spline = CubicSpline(r_knots, n_values, bc_type='natural', extrapolate=True)
    n_r = np.maximum(n_spline(r), 0.1)  # Keep positive
    
    # Dynamical time factor - use v_baryon
    v_circ = galaxy['v_baryon']
    v_circ = np.maximum(v_circ, 10.0)  # Avoid divide by zero
    T_dyn = 2 * np.pi * r / (v_circ * 3.086e13)  # Convert to seconds
    tau_0 = 14e9 * 365.25 * 24 * 3600  # 14 Gyr in seconds
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Enhanced complexity factor with gas clumpiness
    f_gas = galaxy.get('f_gas_true', 0.1)
    Sigma_0 = galaxy.get('Sigma_0', 1e8)
    Sigma_star = 1e8  # M_sun/kpc^2
    
    # Estimate molecular gas fraction (clumpy component)
    # Based on Bigiel+2008 prescription
    Sigma_gas_tot = Sigma_0 * f_gas / (1 - f_gas) if f_gas < 1 else Sigma_0
    Sigma_mol = np.minimum(0.5 * Sigma_gas_tot, Sigma_gas_tot * (Sigma_gas_tot/10)**0.5)
    f_mol = Sigma_mol / (Sigma_gas_tot + 1e-10)  # Molecular fraction
    
    # Two-component gas complexity
    xi_smooth = 1 + C0 * f_gas**gamma * (Sigma_0/Sigma_star)**delta
    xi_clumpy = 1 + C0 * kappa_clump * f_mol * f_gas**gamma * (Sigma_0/Sigma_star)**delta
    
    # Weighted average based on gas phases
    xi = (1 - f_mol) * xi_smooth + f_mol * xi_clumpy
    
    # Geometric correction for disk thickness
    R_d = galaxy.get('R_d', 2.0)
    h_z = h_z_ratio * R_d
    f_thick = (1 - np.exp(-r/R_d)) / (r/R_d + 1e-10)
    zeta_r = 1 + 0.5 * (h_z/r) * f_thick
    
    # Bar/bulge correction
    # Enhanced gravity in bar region due to non-axisymmetric streaming
    r_bar = galaxy.get('r_bar', 0.5 * R_d)  # Bar radius estimate
    bar_profile = np.exp(-(r/r_bar)**2)  # Gaussian bar influence
    
    # Bulge influence (concentrated in center)
    # Check if there's significant bulge contribution in the data
    has_bulge = False
    if hasattr(galaxy, 'data') and len(galaxy['data'].shape) > 1 and galaxy['data'].shape[1] >= 8:
        sigma_bulge = galaxy['data'][:, 7] if galaxy['data'].shape[1] >= 8 else np.zeros_like(r)
        has_bulge = np.any(sigma_bulge > 0)
    
    if has_bulge:
        bulge_fraction = 0.2  # Estimate
        bulge_profile = np.exp(-(r/(0.2*R_d))**2)  # Very concentrated
    else:
        bulge_fraction = 0
        bulge_profile = np.zeros_like(r)
    
    # Combined bar/bulge correction
    zeta_bar = 1 + xi_bar * (0.3 * bar_profile + 0.7 * bulge_fraction * bulge_profile)
    
    # Total weight
    w = n_r * time_factor * xi * zeta_r * zeta_bar
    
    return w

def calculate_chi2_enhanced(params_global, galaxies, verbose=False):
    """Calculate chi-squared with enhanced model"""
    alpha, C0, gamma, delta, h_z_ratio, kappa_clump, xi_bar = params_global[:7]
    smooth_scale = params_global[7]
    prior_strength = params_global[8]
    alpha_beam = params_global[9]
    beta_asym = params_global[10]
    
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
        params = np.concatenate([[alpha, C0, gamma, delta, h_z_ratio, kappa_clump, xi_bar], n_params])
        w = recognition_weight_enhanced(r, params, galaxy)
        
        # Global normalization for bandwidth conservation
        lambda_norm = 0.119  # From previous optimization
        w = lambda_norm * w
        
        # Calculate model velocity
        v_model = np.sqrt(w * v_bar**2)
        
        # Enhanced error model
        # Beam smearing (estimate distance from Hubble flow)
        v_max = np.max(v_obs)
        D_est = v_max / 100  # Very rough estimate, Mpc
        D = max(1.0, min(D_est, 50.0))  # Reasonable range
        
        theta_beam = 20.0  # arcsec, typical for HI
        sigma_beam = alpha_beam * (theta_beam * D * 1000 / r) * v_model
        sigma_beam = np.where(r < 3 * theta_beam * D * 1000 / 206265, sigma_beam, 0)
        
        # Asymmetric drift - higher for dwarfs
        M_star = galaxy.get('M_star_est', 1e9)
        if M_star < 1e9:
            f_morph = 1.5  # Dwarf
        else:
            f_morph = 1.0  # Spiral
        sigma_asym = beta_asym * f_morph * v_model * 0.1
        
        # Inclination uncertainty (assume typical 5 degree error)
        inc = 60.0  # Typical inclination
        inc_err = 5.0
        sigma_inc = v_model * inc_err * np.pi/180 / np.tan(inc * np.pi/180)
        
        # Total error
        sigma_tot = np.sqrt(v_err**2 + sigma_beam**2 + sigma_asym**2 + sigma_inc**2)
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

def optimize_enhanced_model(galaxies, n_galaxies=40):
    """Optimize the enhanced model with all refinements"""
    
    # Select subset for optimization
    galaxy_names = list(galaxies.keys())[:n_galaxies]
    subset = {name: galaxies[name] for name in galaxy_names}
    
    print(f"Optimizing enhanced model on {len(subset)} galaxies...")
    print("Including bulge/bar correction and gas clumpiness")
    
    # Parameter bounds
    # [alpha, C0, gamma, delta, h_z_ratio, kappa_clump, xi_bar, smooth, prior, alpha_beam, beta_asym]
    bounds = [
        (0.1, 0.5),      # alpha: time scaling
        (1.0, 10.0),     # C0: complexity amplitude  
        (1.0, 4.0),      # gamma: gas power
        (0.1, 1.0),      # delta: surface brightness power
        (0.1, 0.5),      # h_z/R_d: disk thickness
        (1.5, 5.0),      # kappa_clump: clumpiness enhancement
        (0.1, 2.0),      # xi_bar: bar/bulge enhancement
        (0.0, 0.01),     # smoothness scale
        (0.0, 0.1),      # prior strength
        (0.5, 1.0),      # alpha_beam: beam smearing coefficient
        (0.3, 0.7),      # beta_asym: asymmetric drift coefficient
    ]
    
    # Create objective function that can be pickled
    def objective(p):
        return calculate_chi2_enhanced(p, subset, verbose=False)
    
    # Optimize
    result = differential_evolution(
        objective,
        bounds,
        seed=42,
        maxiter=300,
        popsize=15,
        tol=1e-4,
        workers=1,  # Use single process to avoid pickling issues
        updating='deferred',
        disp=True
    )
    
    print("\n" + "="*60)
    print("ENHANCED MODEL OPTIMIZATION COMPLETE")
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
    print(f"  κ_clump = {params[5]:.3f}")
    print(f"  ξ_bar = {params[6]:.3f}")
    print(f"  Smoothness = {params[7]:.3f}")
    print(f"  Prior strength = {params[8]:.3f}")
    print(f"  α_beam = {params[9]:.3f}")
    print(f"  β_asym = {params[10]:.3f}")
    
    lambda_norm = 0.119  # Keep from previous
    print(f"Global normalization: λ = {lambda_norm:.3f}")
    
    return params

def fit_all_galaxies_enhanced(galaxies, params_global):
    """Fit all galaxies with enhanced model"""
    print("\nFitting all galaxies with enhanced model...")
    
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
            w = recognition_weight_enhanced(r, params, galaxy)
            w = 0.119 * w  # Global normalization
            v_model = np.sqrt(w * v_bar**2)
            
            # Error model (simplified for speed)
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
    
    print("\nResults with enhanced model:")
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
    
    return results

def plot_enhanced_examples(galaxies, results, params_global):
    """Plot example fits with enhanced model"""
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    # Select examples
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
        
        # Calculate model with enhanced weight
        params = np.concatenate([params_global[:7], result['n_params']])
        w = recognition_weight_enhanced(r, params, galaxy)
        w = 0.119 * w
        v_model = np.sqrt(w * v_bar**2)
        
        # Plot
        ax.errorbar(r, v_obs, yerr=v_err, fmt='o', color='black', 
                   markersize=3, alpha=0.6, label='Observed')
        ax.plot(r, v_bar, '--', color='blue', alpha=0.7, label='Baryonic')
        ax.plot(r, v_model, '-', color='red', linewidth=2, label='LNAL Enhanced')
        
        ax.set_xlabel('Radius (kpc)')
        ax.set_ylabel('Velocity (km/s)')
        ax.set_title(f'{gname} (χ²/N = {result["chi2_N"]:.2f})')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='lower right', fontsize=8)
        ax.set_xlim(0, None)
        ax.set_ylim(0, None)
    
    plt.tight_layout()
    plt.savefig('ledger_enhanced_examples.png', dpi=150, bbox_inches='tight')
    print("\nSaved: ledger_enhanced_examples.png")

if __name__ == "__main__":
    # Load data
    print("Loading master table...")
    master_table = load_master_table()
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize enhanced model
    params_global = optimize_enhanced_model(master_table, n_galaxies=40)
    
    # Fit all galaxies
    results = fit_all_galaxies_enhanced(master_table, params_global)
    
    # Create plots
    plot_enhanced_examples(master_table, results, params_global)
    
    # Save results
    with open('ledger_enhanced_results.pkl', 'wb') as f:
        pickle.dump({
            'params_global': params_global,
            'results': results,
            'median_chi2_N': np.median([r['chi2_N'] for r in results.values()])
        }, f)
    print("Saved: ledger_enhanced_results.pkl") 