#!/usr/bin/env python3
"""
LNAL Dynamic Forward Model
==========================
Forward model with time-varying a₀ based on recognition urgency U(r,t).
Implements bandwidth triage mechanism from Recognition Science.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import cumulative_trapezoid
from scipy.ndimage import gaussian_filter1d
from scipy.optimize import minimize, differential_evolution
import json
import os
from typing import Dict, Tuple, Optional, Callable

# Constants
G = 6.67430e-11  # m³/kg/s²
a_0_base = 1.195e-10  # m/s² (base MOND scale from LNAL)
kpc = 3.0856775814913673e19  # m
pc = kpc / 1000
M_sun = 1.98847e30  # kg
tau_0 = 7.33e-15  # s (fundamental tick)
phi = 1.6180339887  # golden ratio


def exponential_disk(r: np.ndarray, M_disk: float, R_d: float) -> np.ndarray:
    """Exponential disk surface density profile."""
    Sigma_0 = M_disk / (2 * np.pi * R_d**2)
    return Sigma_0 * np.exp(-r / R_d)


def gas_profile(r: np.ndarray, M_gas: float, R_g: float, n: float = 1.0) -> np.ndarray:
    """Gas surface density profile (Sersic-like)."""
    Sigma_0 = M_gas / (2 * np.pi * R_g**2 * n)
    return Sigma_0 * np.exp(-(r / R_g)**(1/n))


def bulge_profile(r: np.ndarray, M_bulge: float, R_b: float) -> np.ndarray:
    """Bulge contribution (projected from 3D Hernquist profile)."""
    Sigma_0 = M_bulge / (2 * np.pi * R_b**2)
    x = r / R_b
    return Sigma_0 * x / (1 + x**2)**2


def compute_urgency(r: np.ndarray, Sigma_total: np.ndarray, v_circ: np.ndarray,
                   complexity_factor: float = 1.0) -> np.ndarray:
    """
    Compute recognition urgency U(r) based on local dynamics.
    
    U(r) = τ₀ * d/dt[log(ρ_R(r))]
    
    Where ρ_R is recognition density, approximated by:
    - Surface density gradients (structure complexity)
    - Velocity shear (dynamical complexity)
    - Turbulent/chaotic motion indicators
    """
    # Avoid divide by zero
    eps = 1e-30
    
    # Spatial recognition density from surface density gradients
    if len(r) > 1:
        # Compute logarithmic derivative of surface density
        d_log_Sigma = np.gradient(np.log(Sigma_total + eps), r)
        
        # Velocity shear contribution
        d_v = np.gradient(v_circ, r)
        shear_term = np.abs(d_v) / (v_circ + eps)
        
        # Combined recognition density rate
        # Higher gradients = more recognition events needed
        rho_R_rate = np.abs(d_log_Sigma) + shear_term
        
        # Apply complexity factor (e.g., for gas turbulence, star formation)
        rho_R_rate *= complexity_factor
        
        # Urgency is logarithmic time derivative
        # For steady state, use characteristic timescale
        t_dyn = r / (v_circ + eps)  # dynamical time
        U = tau_0 * rho_R_rate / t_dyn
        
    else:
        U = np.zeros_like(r)
    
    return U


def dynamic_a0(r: np.ndarray, urgency: np.ndarray, kappa: float = 1.0) -> np.ndarray:
    """
    Compute dynamic MOND scale a₀(r) based on urgency.
    
    a₀(r) = a₀_base * [1 + κ * U(r)]
    
    Parameters:
    -----------
    r : array
        Radial positions
    urgency : array
        Recognition urgency U(r)
    kappa : float
        Coupling constant (order unity from cosmic budget)
    """
    return a_0_base * (1 + kappa * urgency)


def forward_model_galaxy_dynamic(r: np.ndarray, params: Dict, obs_params: Dict,
                               urgency_func: Optional[Callable] = None,
                               kappa: float = 1.0) -> Tuple[np.ndarray, Dict]:
    """
    Forward model galaxy rotation curve with dynamic a₀.
    
    Parameters:
    -----------
    r : array
        Radial positions in meters
    params : dict
        M_disk, R_d, M_gas, R_g, M_bulge, R_b, complexity_factor
    obs_params : dict
        beam_fwhm, inclination, h_z
    urgency_func : callable, optional
        Custom urgency function U(r, Sigma, v)
    kappa : float
        Urgency coupling constant
    """
    # Generate surface density profiles
    Sigma_disk = exponential_disk(r, params['M_disk'], params['R_d'])
    Sigma_gas = gas_profile(r, params['M_gas'], params['R_g'])
    Sigma_bulge = bulge_profile(r, params.get('M_bulge', 0), 
                               params.get('R_b', params['R_d']))
    
    # Total surface density
    Sigma_total = Sigma_disk + Sigma_gas + Sigma_bulge
    
    # Compute enclosed mass
    if len(r) > 1:
        M_enc = 2 * np.pi * cumulative_trapezoid(r * Sigma_total, r, initial=0)
    else:
        M_enc = np.zeros_like(r)
    
    # Newtonian acceleration
    g_newton = G * M_enc / r**2
    g_newton[0] = g_newton[1] if len(g_newton) > 1 else 0
    
    # First pass: get approximate velocity for urgency calculation
    x_approx = g_newton / a_0_base
    mu_approx = x_approx / np.sqrt(1 + x_approx**2)
    g_approx = g_newton / mu_approx
    v_approx = np.sqrt(r * g_approx)
    
    # Compute urgency
    if urgency_func is not None:
        urgency = urgency_func(r, Sigma_total, v_approx)
    else:
        complexity = params.get('complexity_factor', 1.0)
        urgency = compute_urgency(r, Sigma_total, v_approx, complexity)
    
    # Dynamic a₀
    a_0_dynamic = dynamic_a0(r, urgency, kappa)
    
    # LNAL modification with dynamic a₀
    x = g_newton / a_0_dynamic
    
    # Use standard MOND interpolation function (which works!)
    # μ(x) = x/√(1+x²)
    mu = x / np.sqrt(1 + x**2)
    
    # Modified acceleration
    g_total = g_newton / mu
    
    # Circular velocity
    v_circ = np.sqrt(r * g_total)
    
    # Apply observational effects (same as original)
    # Vertical structure correction
    if 'h_z' in obs_params:
        z_corr = 1.0 + (obs_params['h_z'] / params['R_d']) * np.exp(-r / params['R_d'])
        v_circ = v_circ * np.sqrt(z_corr)
    
    # Project to line-of-sight
    if 'inclination' in obs_params:
        v_los = v_circ * np.sin(np.radians(obs_params['inclination']))
    else:
        v_los = v_circ
    
    # Apply beam smearing
    if 'beam_fwhm' in obs_params and len(r) > 1:
        sigma = obs_params['beam_fwhm'] / (2 * np.sqrt(2 * np.log(2)))
        dr = np.median(np.diff(r))
        sigma_points = sigma / dr
        if sigma_points > 0.1:
            v_observed = gaussian_filter1d(v_los, sigma_points, mode='nearest')
        else:
            v_observed = v_los.copy()
    else:
        v_observed = v_los
    
    # Return results with additional diagnostics
    return v_observed, {
        'Sigma_disk': Sigma_disk,
        'Sigma_gas': Sigma_gas,
        'Sigma_bulge': Sigma_bulge,
        'Sigma_total': Sigma_total,
        'v_circ': v_circ,
        'v_los': v_los,
        'v_observed': v_observed,
        'urgency': urgency,
        'a_0_dynamic': a_0_dynamic,
        'mu_values': mu,
        'x_values': x
    }


def fit_dynamic_model(r: np.ndarray, v_obs: np.ndarray, v_err: np.ndarray,
                     initial_params: Dict, obs_params: Dict,
                     fit_kappa: bool = True,
                     kappa_bounds: Tuple[float, float] = (0.1, 10.0)) -> Tuple[Dict, float, object]:
    """
    Fit dynamic forward model to observed data.
    
    Parameters:
    -----------
    r : array
        Radial positions
    v_obs : array
        Observed velocities
    v_err : array
        Velocity errors
    initial_params : dict
        Initial parameter guesses
    obs_params : dict
        Observational parameters
    fit_kappa : bool
        Whether to fit κ as a free parameter
    kappa_bounds : tuple
        Bounds for κ if fitting
    """
    
    def chi2(param_array):
        # Unpack parameters
        idx = 0
        params = {
            'M_disk': param_array[idx] * M_sun,
            'R_d': param_array[idx+1] * kpc,
            'M_gas': param_array[idx+2] * M_sun,
            'R_g': param_array[idx+3] * kpc,
        }
        idx += 4
        
        if 'M_bulge' in initial_params and initial_params['M_bulge'] > 0:
            params['M_bulge'] = param_array[idx] * M_sun
            params['R_b'] = param_array[idx+1] * kpc
            idx += 2
        
        params['complexity_factor'] = param_array[idx]
        idx += 1
        
        if fit_kappa:
            kappa = param_array[idx]
        else:
            kappa = 1.0
        
        # Forward model
        v_model, _ = forward_model_galaxy_dynamic(r, params, obs_params, kappa=kappa)
        
        # Chi-squared
        residuals = (v_model - v_obs) / v_err
        return np.sum(residuals**2)
    
    # Initial guess in fitting units
    x0 = [
        initial_params['M_disk'] / M_sun,
        initial_params['R_d'] / kpc,
        initial_params['M_gas'] / M_sun,
        initial_params['R_g'] / kpc
    ]
    
    # Bounds
    bounds = [
        (1e8, 1e12),   # M_disk in M_sun
        (0.1, 20),     # R_d in kpc
        (1e7, 1e11),   # M_gas in M_sun
        (0.1, 50),     # R_g in kpc
    ]
    
    if 'M_bulge' in initial_params and initial_params['M_bulge'] > 0:
        x0.extend([
            initial_params['M_bulge'] / M_sun,
            initial_params.get('R_b', initial_params['R_d']) / kpc
        ])
        bounds.extend([
            (0, 1e11),     # M_bulge in M_sun
            (0.1, 10)      # R_b in kpc
        ])
    
    # Complexity factor
    x0.append(initial_params.get('complexity_factor', 1.0))
    bounds.append((0.1, 10.0))
    
    # Kappa if fitting
    if fit_kappa:
        x0.append(1.0)
        bounds.append(kappa_bounds)
    
    # Use differential evolution for global optimization
    result = differential_evolution(chi2, bounds, seed=42, maxiter=300,
                                  popsize=15, tol=0.01)
    
    # Extract best-fit parameters
    idx = 0
    best_params = {
        'M_disk': result.x[idx] * M_sun,
        'R_d': result.x[idx+1] * kpc,
        'M_gas': result.x[idx+2] * M_sun,
        'R_g': result.x[idx+3] * kpc,
    }
    idx += 4
    
    if 'M_bulge' in initial_params and initial_params['M_bulge'] > 0:
        best_params['M_bulge'] = result.x[idx] * M_sun
        best_params['R_b'] = result.x[idx+1] * kpc
        idx += 2
    
    best_params['complexity_factor'] = result.x[idx]
    idx += 1
    
    if fit_kappa:
        best_kappa = result.x[idx]
    else:
        best_kappa = 1.0
    
    return best_params, best_kappa, result


def analyze_galaxy_dynamic(galaxy_name: str, rotmod_dir: str = 'Rotmod_LTG',
                         fit_kappa: bool = True) -> Optional[Dict]:
    """Analyze galaxy with dynamic LNAL model."""
    # Load data
    from lnal_sparc_loader_fixed import load_sparc_galaxy_fixed
    galaxy_data = load_sparc_galaxy_fixed(galaxy_name, rotmod_dir)
    
    if galaxy_data is None:
        return None
    
    r = galaxy_data.r
    v_obs = galaxy_data.v_obs
    v_err = galaxy_data.v_err
    
    # Estimate observational parameters
    obs_params = {
        'beam_fwhm': 1.0 * kpc,  # 1 kpc beam
        'inclination': 60,  # degrees, typical
        'h_z': 0.2 * kpc  # scale height
    }
    
    # Initial parameter guess
    v_flat = np.median(v_obs[len(v_obs)//2:])
    R_opt = r[np.argmax(v_obs)] / 2
    
    initial_params = {
        'M_disk': 5e10 * M_sun,
        'R_d': R_opt,
        'M_gas': 1e10 * M_sun,
        'R_g': 2 * R_opt,
        'M_bulge': 1e9 * M_sun if galaxy_name.startswith('NGC') else 0,
        'R_b': 0.2 * R_opt,
        'complexity_factor': 1.0
    }
    
    # Fit
    print(f"Fitting {galaxy_name} with dynamic LNAL model...")
    best_params, best_kappa, opt_result = fit_dynamic_model(
        r, v_obs, v_err, initial_params, obs_params, fit_kappa=fit_kappa
    )
    
    # Generate best-fit model
    v_model, components = forward_model_galaxy_dynamic(
        r, best_params, obs_params, kappa=best_kappa
    )
    
    chi2 = opt_result.fun
    chi2_reduced = chi2 / len(r)
    
    # Also compute static model for comparison
    static_params = best_params.copy()
    v_static, _ = forward_model_galaxy_dynamic(
        r, static_params, obs_params, kappa=0.0  # κ=0 gives static a₀
    )
    
    return {
        'galaxy': galaxy_name,
        'r': r,
        'v_obs': v_obs,
        'v_err': v_err,
        'v_model': v_model,
        'v_static': v_static,
        'components': components,
        'best_params': best_params,
        'best_kappa': best_kappa,
        'obs_params': obs_params,
        'chi2': chi2,
        'chi2_reduced': chi2_reduced,
        'success': opt_result.success
    }


def plot_dynamic_model_fit(result: Dict, save_path: Optional[str] = None):
    """Plot dynamic model fit results."""
    fig, axes = plt.subplots(2, 3, figsize=(16, 10))
    
    r_kpc = result['r'] / kpc
    components = result['components']
    
    # Surface density profiles
    ax = axes[0, 0]
    Sigma_scale = (pc/M_sun)**2
    
    ax.semilogy(r_kpc, components['Sigma_gas'] * Sigma_scale, 'g-', 
                label='Gas', linewidth=2)
    ax.semilogy(r_kpc, components['Sigma_disk'] * Sigma_scale, 'b-', 
                label='Disk', linewidth=2)
    if np.any(components['Sigma_bulge'] > 0):
        ax.semilogy(r_kpc, components['Sigma_bulge'] * Sigma_scale, 'r-', 
                    label='Bulge', linewidth=2)
    ax.semilogy(r_kpc, components['Sigma_total'] * Sigma_scale, 'k-', 
                label='Total', linewidth=2.5)
    
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('Σ [M⊙/pc²]')
    ax.set_title('Surface Density Profiles')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0.1, 1e4)
    
    # Rotation curves
    ax = axes[0, 1]
    ax.errorbar(r_kpc, result['v_obs']/1000, yerr=result['v_err']/1000,
                fmt='ko', markersize=4, label='Observed', alpha=0.7)
    ax.plot(r_kpc, result['v_model']/1000, 'r-', linewidth=2.5,
            label=f'Dynamic LNAL (κ={result["best_kappa"]:.2f})')
    ax.plot(r_kpc, result['v_static']/1000, 'b--', linewidth=2,
            label='Static LNAL', alpha=0.7)
    
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('Velocity [km/s]')
    ax.set_title(f"{result['galaxy']} - χ²/N = {result['chi2_reduced']:.2f}")
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Urgency profile
    ax = axes[0, 2]
    ax.semilogy(r_kpc, components['urgency'], 'purple', linewidth=2)
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('Urgency U(r)')
    ax.set_title('Recognition Urgency')
    ax.grid(True, alpha=0.3)
    
    # Dynamic a₀ profile
    ax = axes[1, 0]
    ax.plot(r_kpc, components['a_0_dynamic']/a_0_base, 'orange', linewidth=2)
    ax.axhline(y=1, color='k', linestyle='--', alpha=0.5)
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('a₀(r) / a₀')
    ax.set_title('Dynamic MOND Scale')
    ax.grid(True, alpha=0.3)
    
    # Transition function
    ax = axes[1, 1]
    ax.semilogx(components['x_values'], components['mu_values'], 'green', linewidth=2)
    ax.set_xlabel('x = g_N / a₀(r)')
    ax.set_ylabel('μ(x)')
    ax.set_title('MOND Interpolation Function')
    ax.grid(True, alpha=0.3)
    
    # Residuals
    ax = axes[1, 2]
    residuals = (result['v_model'] - result['v_obs']) / result['v_err']
    ax.scatter(r_kpc, residuals, c='purple', s=30)
    ax.axhline(y=0, color='k', linestyle='--')
    ax.set_xlabel('Radius [kpc]')
    ax.set_ylabel('(Model - Obs) / Error')
    ax.set_title('Normalized Residuals')
    ax.grid(True, alpha=0.3)
    ax.set_ylim(-5, 5)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150)
        plt.close()
    
    return fig


def analyze_sparc_sample(galaxy_list: list, output_dir: str = 'lnal_dynamic_results',
                        fit_kappa: bool = True) -> list:
    """Analyze a sample of SPARC galaxies with dynamic model."""
    os.makedirs(output_dir, exist_ok=True)
    
    results = []
    
    for galaxy in galaxy_list:
        print(f"\nAnalyzing {galaxy}...")
        result = analyze_galaxy_dynamic(galaxy, fit_kappa=fit_kappa)
        
        if result is not None:
            # Plot
            plot_dynamic_model_fit(
                result,
                save_path=os.path.join(output_dir, f'{galaxy}_dynamic.png')
            )
            
            # Store summary
            results.append({
                'galaxy': galaxy,
                'chi2': result['chi2'],
                'chi2_reduced': result['chi2_reduced'],
                'kappa': result['best_kappa'],
                'n_data': len(result['r']),
                'success': result['success']
            })
            
            print(f"  χ²/N = {result['chi2_reduced']:.2f}, κ = {result['best_kappa']:.2f}")
    
    # Save summary
    with open(os.path.join(output_dir, 'dynamic_model_summary.json'), 'w') as f:
        json.dump({
            'description': 'LNAL analysis with dynamic a₀(r) based on recognition urgency',
            'method': 'Dynamic MOND scale from bandwidth triage mechanism',
            'fit_kappa': fit_kappa,
            'galaxies': results
        }, f, indent=2)
    
    return results


if __name__ == "__main__":
    print("LNAL Dynamic Forward Model Analysis")
    print("=" * 70)
    print("Implementing bandwidth triage mechanism:")
    print("- Recognition urgency U(r) from local dynamics")
    print("- Dynamic MOND scale a₀(r) = a₀[1 + κU(r)]")
    print("- Global coupling constant κ from cosmic budget")
    print("=" * 70)
    
    # Test on problematic galaxies where static model fails
    test_galaxies = [
        'NGC3198',   # High surface brightness spiral
        'NGC2403',   # Another HSB spiral
        'NGC6503',   # Edge-on disk
        'DDO154',    # Dwarf irregular
        'NGC2841',   # Sa galaxy
        'UGC2885'    # Giant LSB galaxy
    ]
    
    # First fit with κ as free parameter
    print("\nPhase 1: Fitting with κ as free parameter...")
    results_free = analyze_sparc_sample(test_galaxies[:4], 
                                       output_dir='lnal_dynamic_results_free',
                                       fit_kappa=True)
    
    # Extract median κ
    kappa_values = [r['kappa'] for r in results_free if r['success']]
    if kappa_values:
        median_kappa = np.median(kappa_values)
        print(f"\nMedian κ from free fits: {median_kappa:.2f}")
    
    # Summary statistics
    chi2_values = [r['chi2_reduced'] for r in results_free]
    print(f"\n{'='*60}")
    print(f"Dynamic model with free κ:")
    print(f"  Mean χ²/N: {np.mean(chi2_values):.2f}")
    print(f"  Min χ²/N: {np.min(chi2_values):.2f}")
    print(f"  Max χ²/N: {np.max(chi2_values):.2f}")
    print(f"  κ range: [{np.min(kappa_values):.2f}, {np.max(kappa_values):.2f}]")
    
    print(f"\nResults saved to lnal_dynamic_results_free/")
