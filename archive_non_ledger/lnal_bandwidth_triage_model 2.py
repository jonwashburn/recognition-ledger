#!/usr/bin/env python3
"""
LNAL Bandwidth Triage Model
===========================
Implements the recognition weight formalism for galaxy rotation curves.
Based on consciousness bandwidth allocation mechanism.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import differential_evolution
import json
import os
from typing import Dict, Tuple, Optional
import pickle
import glob

# Constants
kpc = 3.0856775814913673e19  # m
pc = kpc / 1000
M_sun = 1.98847e30  # kg
G = 6.67430e-11  # m³/kg/s²
tau_0 = 14e9 * 365.25 * 24 * 3600  # 14 Gyr in seconds
Sigma_star = 1e8  # M_sun/kpc² (characteristic surface brightness)


def load_sparc_data():
    """Load SPARC data from Rotmod_LTG directory"""
    sparc_data = {}
    
    # Get all rotmod files (excluding duplicates with " 2.dat")
    rotmod_files = glob.glob('Rotmod_LTG/*_rotmod.dat')
    rotmod_files = [f for f in rotmod_files if ' 2.dat' not in f]
    
    for filepath in rotmod_files:
        # Extract galaxy name
        galaxy_name = os.path.basename(filepath).replace('_rotmod.dat', '')
        
        try:
            # Read the file
            data = []
            distance = None
            
            with open(filepath, 'r') as f:
                for line in f:
                    if line.startswith('# Distance'):
                        # Extract distance in Mpc
                        distance = float(line.split('=')[1].split('Mpc')[0].strip())
                    elif not line.startswith('#') and line.strip():
                        # Data line
                        parts = line.split()
                        if len(parts) >= 6:
                            data.append([float(x) for x in parts])
            
            if len(data) < 3:  # Skip galaxies with too few points
                continue
                
            data = np.array(data)
            
            # Create curve dictionary
            curve = {
                'r': data[:, 0],        # Radius in kpc
                'V_obs': data[:, 1],    # Observed velocity
                'e_V': data[:, 2],      # Velocity error
                'V_gas': data[:, 3],    # Gas velocity
                'V_disk': data[:, 4],   # Disk velocity
                'V_bul': data[:, 5] if data.shape[1] > 5 else np.zeros(len(data)),  # Bulge velocity
            }
            
            # Create galaxy data structure
            sparc_data[galaxy_name] = {
                'curve': curve,
                'distance': distance,
                'catalog': {}  # Empty catalog for compatibility
            }
            
        except Exception as e:
            print(f"Error loading {galaxy_name}: {e}")
            continue
    
    print(f"Loaded {len(sparc_data)} galaxies from Rotmod_LTG")
    return sparc_data


def recognition_weight(r_kpc, T_dyn, f_gas, Sigma_0, params, R_d=2.0):
    """
    Calculate recognition weight w(r) for bandwidth triage.
    
    w(r) = λ × ξ × n(r) × (T_dyn/τ₀)^α × ζ(r)
    
    Parameters:
    -----------
    r_kpc : array, radii in kpc
    T_dyn : array, dynamical time in seconds
    f_gas : float, gas mass fraction
    Sigma_0 : float, central surface brightness in M_sun/kpc²
    params : dict with keys:
        alpha : time scaling exponent
        C0 : complexity amplitude
        gamma : gas fraction power
        delta : surface brightness power
        lambda_norm : global normalization
    R_d : float, disk scale length in kpc (default 2.0)
        
    Returns:
    --------
    w : array, recognition weight at each radius
    """
    # Unpack parameters
    alpha = params['alpha']
    C0 = params['C0']
    gamma = params['gamma']
    delta = params['delta']
    lambda_norm = params['lambda_norm']
    
    # Complexity factor ξ
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Time-dependent factor
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Radial profile n(r) that varies from ~2 in center to ~10 at large radii
    # As described in the paper
    n_r = 2.0 + 8.0 * (1 - np.exp(-r_kpc / 8.0))  # Smooth transition from 2 to 10
    
    # Geometric correction ζ(r) for disk thickness
    # Paper mentions this is order unity with mild radial dependence
    h_z = 0.25 * R_d  # Typical disk thickness ~0.25 * scale length
    zeta_r = 1 + 0.5 * (h_z / r_kpc) * np.exp(-r_kpc / R_d)
    
    # Total weight
    w = lambda_norm * xi * n_r * time_factor * zeta_r
    
    return w


def calculate_model_velocity(r_kpc, v_baryon, galaxy_props, params):
    """
    Calculate model rotation curve using bandwidth triage.
    
    v_model² = w(r) × v_baryon²
    """
    # Calculate dynamical time at each radius
    # T_dyn = 2πr/v_circ, use baryon velocity as approximation
    v_circ_ms = v_baryon * 1000  # km/s to m/s
    r_m = r_kpc * kpc
    T_dyn = 2 * np.pi * r_m / (v_circ_ms + 1e-10)  # Avoid division by zero
    
    # Get galaxy properties
    f_gas = galaxy_props.get('f_gas', 0.1)
    Sigma_0 = galaxy_props.get('Sigma_0', 1e8)
    R_d = galaxy_props.get('R_d', 2.0)  # Disk scale length
    
    # Calculate recognition weight
    w = recognition_weight(r_kpc, T_dyn, f_gas, Sigma_0, params, R_d)
    
    # Model velocity
    v_model = np.sqrt(w) * v_baryon
    
    return v_model, w


def fit_galaxy(galaxy_name, galaxy_data, params_init=None):
    """Fit a single galaxy with bandwidth triage model"""
    
    # Extract curve data
    curve = galaxy_data['curve']
    if curve is None:
        return None
        
    r_kpc = np.array(curve['r'])
    v_obs = np.array(curve['V_obs'])
    v_err = np.array(curve.get('e_V', np.maximum(0.03 * v_obs, 2.0)))
    
    # Calculate baryon velocity from components
    v_gas = np.array(curve.get('V_gas', np.zeros_like(r_kpc)))
    v_disk = np.array(curve.get('V_disk', np.zeros_like(r_kpc)))
    v_bul = np.array(curve.get('V_bul', np.zeros_like(r_kpc)))
    
    v_baryon = np.sqrt(v_gas**2 + v_disk**2 + v_bul**2)
    
    # Estimate galaxy properties
    catalog = galaxy_data.get('catalog', {})
    
    # Gas fraction (from catalog or estimate from velocities)
    if 'M_gas' in catalog and 'M_star' in catalog:
        M_gas = catalog['M_gas'] * 1e9  # Convert to M_sun
        M_star = catalog['M_star'] * 1e9
        f_gas = M_gas / (M_gas + M_star) if (M_gas + M_star) > 0 else 0.1
    else:
        # Rough estimate from velocity contributions
        f_gas = np.mean(v_gas**2) / (np.mean(v_baryon**2) + 1e-10)
    
    # Surface brightness (estimate from velocities and radii)
    # Simplified: use peak baryon velocity and radius
    v_peak = np.max(v_baryon)
    r_peak = r_kpc[np.argmax(v_baryon)]
    Sigma_0 = (v_peak**2 * r_peak / G) * (1e-9 / kpc**2) * 1e10  # Very rough estimate
    
    # Estimate disk scale length from velocity profile
    # R_d is typically where v reaches ~63% of maximum
    v_max = np.max(v_baryon)
    idx_63 = np.argmin(np.abs(v_baryon - 0.63 * v_max))
    R_d = r_kpc[idx_63] if idx_63 > 0 else 2.0
    
    galaxy_props = {
        'f_gas': f_gas,
        'Sigma_0': Sigma_0,
        'R_d': R_d
    }
    
    # Define chi-squared function
    def chi2_func(param_array):
        params = {
            'alpha': param_array[0],
            'C0': param_array[1],
            'gamma': param_array[2],
            'delta': param_array[3],
            'lambda_norm': param_array[4]
        }
        
        v_model, _ = calculate_model_velocity(r_kpc, v_baryon, galaxy_props, params)
        
        residuals = (v_model - v_obs) / v_err
        return np.sum(residuals**2)
    
    # Parameter bounds
    bounds = [
        (0.1, 0.5),    # alpha: time scaling exponent
        (0.1, 10.0),   # C0: complexity amplitude
        (0.5, 4.0),    # gamma: gas fraction power
        (0.1, 1.0),    # delta: surface brightness power
        (0.01, 1.0)    # lambda_norm: global normalization
    ]
    
    # Initial guess or use provided
    if params_init is None:
        x0 = [0.2, 5.0, 3.0, 0.2, 0.12]  # From paper
    else:
        x0 = [params_init[k] for k in ['alpha', 'C0', 'gamma', 'delta', 'lambda_norm']]
    
    # Optimize
    result = differential_evolution(chi2_func, bounds, seed=42, maxiter=200)
    
    # Extract best parameters
    best_params = {
        'alpha': result.x[0],
        'C0': result.x[1],
        'gamma': result.x[2],
        'delta': result.x[3],
        'lambda_norm': result.x[4]
    }
    
    # Calculate final model
    v_model, w = calculate_model_velocity(r_kpc, v_baryon, galaxy_props, best_params)
    
    chi2 = result.fun
    chi2_reduced = chi2 / len(r_kpc)
    
    return {
        'galaxy': galaxy_name,
        'r_kpc': r_kpc,
        'v_obs': v_obs,
        'v_err': v_err,
        'v_baryon': v_baryon,
        'v_model': v_model,
        'recognition_weight': w,
        'best_params': best_params,
        'galaxy_props': galaxy_props,
        'chi2': chi2,
        'chi2_reduced': chi2_reduced,
        'success': result.success
    }


def global_optimization(galaxy_sample, output_dir='bandwidth_triage_results'):
    """
    Perform global optimization on a sample of galaxies.
    First find global parameters, then apply to all galaxies.
    """
    os.makedirs(output_dir, exist_ok=True)
    
    # Load SPARC data
    print("Loading SPARC data...")
    sparc_data = load_sparc_data()
    
    # Select galaxies for optimization
    if galaxy_sample == 'all':
        galaxy_list = list(sparc_data.keys())
    else:
        galaxy_list = galaxy_sample
    
    print(f"Optimizing on {len(galaxy_list)} galaxies")
    
    # Global optimization function
    def global_chi2(param_array):
        params = {
            'alpha': param_array[0],
            'C0': param_array[1],
            'gamma': param_array[2],
            'delta': param_array[3],
            'lambda_norm': param_array[4]
        }
        
        total_chi2 = 0
        total_n = 0
        
        for galaxy_name in galaxy_list:  # Use all galaxies for optimization
            if galaxy_name not in sparc_data:
                continue
                
            result = fit_galaxy(galaxy_name, sparc_data[galaxy_name], params)
            if result is not None:
                total_chi2 += result['chi2']
                total_n += len(result['r_kpc'])
        
        return total_chi2 / total_n if total_n > 0 else 1e10
    
    # Global parameter bounds
    bounds = [
        (0.1, 0.5),    # alpha
        (0.1, 10.0),   # C0
        (0.5, 4.0),    # gamma
        (0.1, 1.0),    # delta
        (0.01, 1.0)    # lambda_norm
    ]
    
    print("Running global optimization...")
    result = differential_evolution(global_chi2, bounds, seed=42, 
                                  maxiter=100, popsize=15, disp=True)
    
    # Extract global best parameters
    global_params = {
        'alpha': result.x[0],
        'C0': result.x[1],
        'gamma': result.x[2],
        'delta': result.x[3],
        'lambda_norm': result.x[4]
    }
    
    print("\nGlobal best parameters:")
    for k, v in global_params.items():
        print(f"  {k}: {v:.3f}")
    
    # Apply to all galaxies
    print(f"\nApplying to all {len(sparc_data)} galaxies...")
    all_results = []
    chi2_values = []
    
    for galaxy_name, galaxy_data in sparc_data.items():
        result = fit_galaxy(galaxy_name, galaxy_data, global_params)
        if result is not None:
            all_results.append(result)
            chi2_values.append(result['chi2_reduced'])
            
            # Plot some examples
            if len(all_results) <= 6:
                plot_galaxy_fit(result, 
                              save_path=os.path.join(output_dir, f'{galaxy_name}_fit.png'))
    
    # Statistics
    chi2_values = np.array(chi2_values)
    print(f"\n{'='*60}")
    print("BANDWIDTH TRIAGE MODEL RESULTS")
    print(f"{'='*60}")
    print(f"Galaxies analyzed: {len(chi2_values)}")
    print(f"Median χ²/N: {np.median(chi2_values):.3f}")
    print(f"Mean χ²/N: {np.mean(chi2_values):.3f}")
    print(f"Best χ²/N: {np.min(chi2_values):.3f}")
    print(f"Worst χ²/N: {np.max(chi2_values):.3f}")
    print(f"Fraction with χ²/N < 1: {np.sum(chi2_values < 1)/len(chi2_values)*100:.1f}%")
    print(f"Fraction with χ²/N < 2: {np.sum(chi2_values < 2)/len(chi2_values)*100:.1f}%")
    
    # Save results
    summary = {
        'global_params': global_params,
        'statistics': {
            'n_galaxies': len(chi2_values),
            'median_chi2': float(np.median(chi2_values)),
            'mean_chi2': float(np.mean(chi2_values)),
            'min_chi2': float(np.min(chi2_values)),
            'max_chi2': float(np.max(chi2_values)),
            'frac_good': float(np.sum(chi2_values < 2)/len(chi2_values))
        },
        'individual_results': [
            {
                'galaxy': r['galaxy'],
                'chi2_reduced': r['chi2_reduced'],
                'f_gas': r['galaxy_props']['f_gas'],
                'Sigma_0': r['galaxy_props']['Sigma_0']
            }
            for r in all_results
        ]
    }
    
    with open(os.path.join(output_dir, 'bandwidth_triage_summary.json'), 'w') as f:
        json.dump(summary, f, indent=2)
    
    # Chi-squared distribution plot
    plt.figure(figsize=(8, 6))
    plt.hist(chi2_values, bins=30, alpha=0.7, edgecolor='black')
    plt.axvline(1.0, color='red', linestyle='--', label='χ²/N = 1')
    plt.axvline(np.median(chi2_values), color='green', linestyle='--', 
                label=f'Median = {np.median(chi2_values):.2f}')
    plt.xlabel('χ²/N')
    plt.ylabel('Number of galaxies')
    plt.title('Bandwidth Triage Model: χ² Distribution')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.savefig(os.path.join(output_dir, 'chi2_distribution.png'), dpi=150)
    plt.close()
    
    return all_results, global_params


def plot_galaxy_fit(result, save_path=None):
    """Plot galaxy fit with bandwidth triage model"""
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    r_kpc = result['r_kpc']
    
    # Rotation curve
    ax = axes[0, 0]
    ax.errorbar(r_kpc, result['v_obs'], yerr=result['v_err'],
                fmt='ko', markersize=4, label='Observed', alpha=0.7)
    ax.plot(r_kpc, result['v_baryon'], 'b--', linewidth=2,
            label='Baryons (Newton)', alpha=0.7)
    ax.plot(r_kpc, result['v_model'], 'r-', linewidth=2.5,
            label=f'Model (χ²/N={result["chi2_reduced"]:.2f})')
    
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('Velocity [km/s]')
    ax.set_title(result['galaxy'])
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Recognition weight
    ax = axes[0, 1]
    ax.plot(r_kpc, result['recognition_weight'], 'purple', linewidth=2)
    ax.axhline(y=1, color='k', linestyle='--', alpha=0.5)
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('Recognition Weight w(r)')
    ax.set_title('Bandwidth Allocation')
    ax.grid(True, alpha=0.3)
    
    # Residuals
    ax = axes[1, 0]
    residuals = (result['v_model'] - result['v_obs']) / result['v_err']
    ax.scatter(r_kpc, residuals, c='purple', s=30)
    ax.axhline(y=0, color='k', linestyle='--')
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('(Model - Obs) / Error')
    ax.set_title('Normalized Residuals')
    ax.grid(True, alpha=0.3)
    ax.set_ylim(-5, 5)
    
    # Parameters
    ax = axes[1, 1]
    ax.axis('off')
    
    params = result['best_params']
    props = result['galaxy_props']
    
    text = "Best-fit Parameters:\n\n"
    text += f"α (time exponent) = {params['alpha']:.3f}\n"
    text += f"C₀ (complexity) = {params['C0']:.3f}\n"
    text += f"γ (gas power) = {params['gamma']:.3f}\n"
    text += f"δ (SB power) = {params['delta']:.3f}\n"
    text += f"λ (normalization) = {params['lambda_norm']:.3f}\n"
    text += f"\nGalaxy Properties:\n"
    text += f"f_gas = {props['f_gas']:.3f}\n"
    text += f"Σ₀ = {props['Sigma_0']:.1e} M⊙/kpc²\n"
    text += f"\nχ²/N = {result['chi2_reduced']:.3f}"
    
    ax.text(0.1, 0.9, text, transform=ax.transAxes,
            fontsize=11, verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150)
        plt.close()
    
    return fig


if __name__ == "__main__":
    print("LNAL Bandwidth Triage Model")
    print("=" * 70)
    print("Implementing consciousness bandwidth allocation mechanism")
    print("v_model² = w(r) × v_baryon²")
    print("=" * 70)
    
    # Test on a subset first
    test_galaxies = [
        'NGC3198', 'NGC2403', 'NGC6503', 'DDO154',
        'NGC2841', 'UGC2885', 'NGC7814', 'NGC3521'
    ]
    
    # Run global optimization
    results, global_params = global_optimization('all')
    
    print("\nAnalysis complete!") 