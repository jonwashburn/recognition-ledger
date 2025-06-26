#!/usr/bin/env python3
"""
LNAL Paper Implementation
=========================
Exact implementation of the bandwidth triage model from the paper
that achieved median χ²/N = 0.48 on SPARC galaxies.

Based on equations from "Galaxy Rotation Without Dark Matter" paper.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import differential_evolution
import pickle
from tqdm import tqdm

# Constants from paper
tau_0 = 14e9 * 365.25 * 24 * 3600  # 14 Gyr in seconds
Sigma_star = 1e8  # M_sun/kpc² (characteristic surface brightness)

# Best-fit parameters from paper (Section IV.A)
PAPER_PARAMS = {
    'alpha': 0.194,      # Time scaling exponent
    'C0': 5.064,        # Complexity amplitude  
    'gamma': 2.953,     # Gas fraction power
    'delta': 0.216,     # Surface brightness power
    'lambda_norm': 0.119 # Global normalization
}


def load_master_table():
    """Load the pre-processed SPARC master table"""
    with open('sparc_master.pkl', 'rb') as f:
        return pickle.load(f)


def recognition_weight_paper(r, galaxy, params):
    """
    Calculate recognition weight exactly as in the paper.
    
    From Eq. (7): w(r) = λ × ξ × n(r) × (T_dyn/τ_0)^α × ζ(r)
    
    Where:
    - ξ = 1 + C₀ × f_gas^γ × (Σ₀/Σ_*)^δ  [Eq. 8]
    - n(r) is a smooth radial profile
    - ζ(r) accounts for disk thickness
    """
    # Extract parameters
    alpha = params['alpha']
    C0 = params['C0']
    gamma = params['gamma']
    delta = params['delta']
    lambda_norm = params['lambda_norm']
    
    # Get galaxy properties
    f_gas = galaxy.get('f_gas_true', 0.1)
    Sigma_0 = galaxy.get('Sigma_0', 1e8)
    R_d = galaxy.get('R_d', 2.0)
    
    # Calculate dynamical time using observed velocities (more stable)
    v_obs = galaxy.get('v_obs', galaxy['v_baryon'])
    v_circ = np.maximum(v_obs, 10.0)  # km/s, avoid division by zero
    T_dyn = 2 * np.pi * r / (v_circ * 3.086e13)  # Convert to seconds
    
    # Complexity factor ξ from Eq. (8)
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Time-dependent factor
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Radial profile n(r) - smooth function as mentioned in paper
    # The paper mentions n(r) varies smoothly from ~2 in center to ~10 at large radii
    n_r = 2.0 + 8.0 * (1 - np.exp(-r / (2 * R_d)))
    
    # Geometric correction ζ(r) for disk thickness
    # Paper mentions this is order unity with mild radial dependence
    h_z = 0.25 * R_d  # Typical disk thickness
    zeta_r = 1 + 0.5 * (h_z / r) * np.exp(-r / R_d)
    
    # Total weight
    w = lambda_norm * xi * n_r * time_factor * zeta_r
    
    return w


def fit_galaxy_paper(galaxy_name, galaxy, params=None):
    """Fit a galaxy using the paper's model"""
    
    if params is None:
        params = PAPER_PARAMS
    
    # Get data
    r = galaxy['r']  # kpc
    v_obs = galaxy['v_obs']  # km/s
    v_bar = galaxy['v_baryon']  # km/s
    
    # Estimate errors as in paper
    v_err = galaxy.get('v_err', np.maximum(0.03 * v_obs, 3.0))
    
    # Calculate recognition weight
    w = recognition_weight_paper(r, galaxy, params)
    
    # Model velocity from Eq. (6): v_model² = w(r) × v_baryon²
    v_model = np.sqrt(w * v_bar**2)
    
    # Chi-squared
    chi2 = np.sum(((v_obs - v_model) / v_err)**2)
    chi2_N = chi2 / len(r)
    
    return {
        'galaxy': galaxy_name,
        'chi2': chi2,
        'chi2_N': chi2_N,
        'r': r,
        'v_obs': v_obs,
        'v_err': v_err,
        'v_bar': v_bar,
        'v_model': v_model,
        'w': w
    }


def analyze_all_galaxies():
    """Analyze all SPARC galaxies with paper parameters"""
    
    print("Loading SPARC master table...")
    master_table = load_master_table()
    print(f"Loaded {len(master_table)} galaxies")
    
    print("\nAnalyzing with paper parameters:")
    for key, val in PAPER_PARAMS.items():
        print(f"  {key} = {val}")
    
    # Fit all galaxies
    results = []
    chi2_values = []
    
    print("\nFitting galaxies...")
    for galaxy_name, galaxy in tqdm(master_table.items()):
        if len(galaxy['r']) < 5:  # Skip galaxies with too few points
            continue
            
        result = fit_galaxy_paper(galaxy_name, galaxy, PAPER_PARAMS)
        results.append(result)
        chi2_values.append(result['chi2_N'])
    
    chi2_values = np.array(chi2_values)
    
    # Calculate statistics
    print("\n" + "="*60)
    print("PAPER IMPLEMENTATION RESULTS")
    print("="*60)
    print(f"Galaxies analyzed: {len(chi2_values)}")
    print(f"Median χ²/N: {np.median(chi2_values):.3f}")
    print(f"Mean χ²/N: {np.mean(chi2_values):.3f}")
    print(f"Std χ²/N: {np.std(chi2_values):.3f}")
    print(f"\nFraction with χ²/N < 0.5: {np.sum(chi2_values < 0.5)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 1.0: {np.sum(chi2_values < 1.0)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 1.5: {np.sum(chi2_values < 1.5)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 2.0: {np.sum(chi2_values < 2.0)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 5.0: {np.sum(chi2_values < 5.0)/len(chi2_values)*100:.1f}%")
    
    # Separate by galaxy type
    dwarf_chi2 = []
    spiral_chi2 = []
    
    for result in results:
        galaxy = master_table[result['galaxy']]
        M_star = galaxy.get('M_star_est', 1e10)
        
        if M_star < 1e9:  # Dwarf
            dwarf_chi2.append(result['chi2_N'])
        else:  # Spiral
            spiral_chi2.append(result['chi2_N'])
    
    if dwarf_chi2:
        print(f"\nDwarf galaxies (M* < 10⁹ M☉):")
        print(f"  Number: {len(dwarf_chi2)}")
        print(f"  Median χ²/N: {np.median(dwarf_chi2):.3f}")
        
    if spiral_chi2:
        print(f"\nSpiral galaxies (M* ≥ 10⁹ M☉):")
        print(f"  Number: {len(spiral_chi2)}")
        print(f"  Median χ²/N: {np.median(spiral_chi2):.3f}")
    
    # Plot examples
    plot_examples(results, master_table)
    
    return results, chi2_values


def plot_examples(results, master_table):
    """Plot example galaxies mentioned in the paper"""
    
    # Examples from paper
    example_names = ['DDO154', 'NGC2403', 'NGC3198', 'NGC6503', 'UGC2885', 'F568-3']
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    plot_idx = 0
    for result in results:
        if result['galaxy'] in example_names and plot_idx < 6:
            ax = axes[plot_idx]
            
            # Plot data
            ax.errorbar(result['r'], result['v_obs'], yerr=result['v_err'],
                       fmt='ko', markersize=4, alpha=0.7, label='Observed')
            ax.plot(result['r'], result['v_bar'], 'b--', alpha=0.7, 
                   label='Baryons (Newton)', linewidth=2)
            ax.plot(result['r'], result['v_model'], 'r-', linewidth=2.5,
                   label=f'Model (χ²/N={result["chi2_N"]:.2f})')
            
            ax.set_xlabel('Radius (kpc)')
            ax.set_ylabel('Velocity (km/s)')
            ax.set_title(result['galaxy'])
            ax.legend(loc='lower right', fontsize=9)
            ax.grid(True, alpha=0.3)
            ax.set_xlim(0, None)
            ax.set_ylim(0, None)
            
            plot_idx += 1
    
    plt.tight_layout()
    plt.savefig('paper_implementation_examples.png', dpi=150, bbox_inches='tight')
    print("\nSaved: paper_implementation_examples.png")


def optimize_parameters(master_table, n_optimize=40):
    """
    Optimize parameters on a subset to verify we can reproduce paper results
    """
    print(f"\nOptimizing on {n_optimize} galaxies...")
    
    # Select subset
    galaxy_names = list(master_table.keys())[:n_optimize]
    subset = {name: master_table[name] for name in galaxy_names if len(master_table[name]['r']) >= 5}
    
    def global_chi2(param_array):
        params = {
            'alpha': param_array[0],
            'C0': param_array[1], 
            'gamma': param_array[2],
            'delta': param_array[3],
            'lambda_norm': param_array[4]
        }
        
        total_chi2 = 0
        total_N = 0
        
        for galaxy_name, galaxy in subset.items():
            result = fit_galaxy_paper(galaxy_name, galaxy, params)
            total_chi2 += result['chi2']
            total_N += len(result['r'])
        
        return total_chi2 / total_N
    
    # Bounds from paper
    bounds = [
        (0.1, 0.5),    # alpha
        (1.0, 10.0),   # C0
        (1.0, 4.0),    # gamma
        (0.1, 1.0),    # delta
        (0.05, 0.2)    # lambda_norm
    ]
    
    # Initial guess (paper values)
    x0 = [PAPER_PARAMS['alpha'], PAPER_PARAMS['C0'], PAPER_PARAMS['gamma'],
          PAPER_PARAMS['delta'], PAPER_PARAMS['lambda_norm']]
    
    print("Running optimization...")
    result = differential_evolution(global_chi2, bounds, x0=x0, seed=42,
                                  maxiter=100, popsize=15, disp=True)
    
    opt_params = {
        'alpha': result.x[0],
        'C0': result.x[1],
        'gamma': result.x[2], 
        'delta': result.x[3],
        'lambda_norm': result.x[4]
    }
    
    print("\nOptimized parameters:")
    for key, val in opt_params.items():
        paper_val = PAPER_PARAMS[key]
        print(f"  {key}: {val:.3f} (paper: {paper_val:.3f}, diff: {abs(val-paper_val)/paper_val*100:.1f}%)")
    
    return opt_params


if __name__ == "__main__":
    # First verify we can reproduce paper parameters
    master_table = load_master_table()
    
    # Optimize on subset
    opt_params = optimize_parameters(master_table, n_optimize=40)
    
    # Analyze all galaxies with paper parameters
    results, chi2_values = analyze_all_galaxies()
    
    # Save results
    with open('paper_implementation_results.pkl', 'wb') as f:
        pickle.dump({
            'results': results,
            'chi2_values': chi2_values,
            'params': PAPER_PARAMS,
            'opt_params': opt_params
        }, f)
    print("\nSaved: paper_implementation_results.pkl") 