#!/usr/bin/env python3
"""
Morphology-aware ledger solver
Categorizes galaxies and applies appropriate recognition profiles
"""

import numpy as np
import pickle
from scipy.optimize import minimize, differential_evolution
import matplotlib.pyplot as plt

# Constants
G_kpc = 4.302e-6  # kpc (km/s)² / M_sun
tau_0 = 1e8  # years
Sigma_star = 1e8  # M_sun/kpc²

def categorize_galaxy(galaxy_data):
    """
    Categorize galaxy based on properties:
    - dwarf: low mass, low surface brightness
    - spiral: moderate mass, disk-dominated
    - massive: high mass, high surface brightness
    - gas_rich: f_gas > 0.5
    """
    f_gas = galaxy_data['f_gas_true']
    Sigma_0 = galaxy_data['Sigma_0']
    v_max = np.max(galaxy_data['v_obs'])
    
    categories = []
    
    # Primary morphology
    if v_max < 80:  # km/s
        categories.append('dwarf')
    elif v_max > 200 and Sigma_0 > 5e8:
        categories.append('massive')
    else:
        categories.append('spiral')
    
    # Gas content
    if f_gas > 0.5:
        categories.append('gas_rich')
    elif f_gas < 0.1:
        categories.append('gas_poor')
    else:
        categories.append('gas_moderate')
        
    # Surface brightness
    if Sigma_0 < 1e8:
        categories.append('LSB')  # Low surface brightness
    elif Sigma_0 > 1e9:
        categories.append('HSB')  # High surface brightness
        
    return categories

def morphology_weight(r, galaxy_data, params_global, params_morph):
    """
    Recognition weight with morphology-specific parameters
    """
    # Get galaxy categories
    categories = categorize_galaxy(galaxy_data)
    
    # Base parameters
    alpha_base, C0_base, gamma_base, delta_base = params_global[:4]
    
    # Morphology adjustments
    alpha_adj = 0
    C0_adj = 0
    r1_adj = 1.0
    n1_adj = 1.0
    n2_adj = 1.0
    
    # Apply morphology-specific adjustments
    if 'dwarf' in categories:
        alpha_adj += params_morph[0]
        C0_adj += params_morph[1]
        r1_adj *= params_morph[2]
        
    if 'massive' in categories:
        alpha_adj -= params_morph[3]
        n1_adj *= params_morph[4]
        
    if 'gas_rich' in categories:
        C0_adj += params_morph[5]
        n2_adj *= params_morph[6]
        
    if 'LSB' in categories:
        n1_adj *= params_morph[7]
        n2_adj *= params_morph[8]
    
    # Final parameters
    alpha = alpha_base + alpha_adj
    C0 = C0_base * (1 + C0_adj)
    
    # Complexity factor
    f_gas = galaxy_data['f_gas_true']
    Sigma_0 = galaxy_data['Sigma_0']
    xi = 1 + C0 * (f_gas ** gamma_base) * ((Sigma_0 / Sigma_star) ** delta_base)
    
    # Time factor
    T_dyn = galaxy_data['T_dyn']
    time_factor = (T_dyn / tau_0) ** alpha
    
    # Radial profile (morphology-dependent)
    r1 = 0.5 * r1_adj  # kpc
    beta = 2.5
    
    x1 = (r / r1) ** beta
    trans1 = 1 / (1 + x1)
    trans2 = x1 / (1 + x1)
    
    # Base refresh with morphology adjustments
    n_inner = 1.0
    n_disk = 3.0 * n1_adj
    n_outer = 5.0 * n2_adj
    
    # Smooth transitions
    n_base = trans1 * n_inner + trans2 * n_disk
    
    # Outer transition
    r2 = 20.0  # kpc
    x2 = (r / r2) ** beta
    trans3 = x2 / (1 + x2)
    n_total = (1 - trans3) * n_base + trans3 * n_outer
    
    # Total weight
    w = xi * n_total * time_factor
    
    return w

def fit_with_morphology(master_table, params_global, params_morph):
    """
    Fit all galaxies with morphology-aware weights
    """
    # First calculate normalization
    W_tot = 0
    W_Newton = 0
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        dr = np.gradient(r)
        w = morphology_weight(r, galaxy, params_global, params_morph)
        W_tot += np.sum(w * dr)
        W_Newton += np.sum(dr)
        
    lambda_norm = W_Newton / W_tot if W_tot > 0 else 1.0
    
    # Now fit galaxies
    total_chi2 = 0
    total_points = 0
    results = []
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        df = galaxy['data']
        v_err = df['verr'].values
        v_gas = df['vgas'].values
        v_disk = df['vdisk'].values
        v_bul = df['vbul'].values
        
        # Get weights
        w = morphology_weight(r, galaxy, params_global, params_morph)
        G_eff = G_kpc * lambda_norm * w
        
        # Find best M/L
        ml_values = np.linspace(0.1, 5.0, 30)
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
        
        total_chi2 += chi2_best
        total_points += len(v_obs)
        
        results.append({
            'name': name,
            'chi2_reduced': chi2_best / len(v_obs),
            'ml': ml_best,
            'categories': categorize_galaxy(galaxy)
        })
        
    return total_chi2 / total_points, lambda_norm, results

def optimize_morphology_params(master_table, n_galaxies=40):
    """
    Optimize both global and morphology parameters
    """
    # Use subset
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    def objective(params):
        params_global = params[:4]
        params_morph = params[4:]
        chi2, _, _ = fit_with_morphology(subset, params_global, params_morph)
        return chi2
    
    # Initial guess and bounds
    x0 = [
        # Global parameters
        0.5, 5.0, 2.0, 0.3,
        # Morphology adjustments
        0.2, 0.5, 0.8, 0.1, 1.2, 1.0, 1.5, 1.2, 1.3
    ]
    
    bounds = [
        # Global
        (0.0, 1.0), (0.0, 20.0), (1.0, 3.0), (0.0, 1.0),
        # Morphology  
        (-0.5, 0.5), (0.0, 2.0), (0.5, 2.0),  # dwarf
        (-0.5, 0.5), (0.5, 2.0),              # massive
        (0.0, 3.0), (0.5, 3.0),               # gas_rich
        (0.5, 2.0), (0.5, 2.0)                # LSB
    ]
    
    print(f"Optimizing {len(x0)} parameters on {n_galaxies} galaxies...")
    
    result = differential_evolution(objective, bounds, maxiter=25, 
                                  popsize=10, disp=True)
    
    return result.x

def analyze_morphology_results(master_table, params_opt):
    """
    Analyze results by morphology category
    """
    params_global = params_opt[:4]
    params_morph = params_opt[4:]
    
    chi2_global, lambda_norm, results = fit_with_morphology(
        master_table, params_global, params_morph
    )
    
    print(f"\nGlobal normalization: λ = {lambda_norm:.3f}")
    print(f"Average boost: ρ = {1/lambda_norm:.3f}")
    
    # Statistics by category
    category_stats = {}
    
    for res in results:
        for cat in res['categories']:
            if cat not in category_stats:
                category_stats[cat] = []
            category_stats[cat].append(res['chi2_reduced'])
    
    print("\nMedian χ²/N by category:")
    for cat, chi2_list in sorted(category_stats.items()):
        median = np.median(chi2_list)
        print(f"  {cat}: {median:.2f} (N={len(chi2_list)})")
        
    # Overall statistics
    all_chi2 = [r['chi2_reduced'] for r in results]
    print(f"\nOverall statistics:")
    print(f"  Median χ²/N = {np.median(all_chi2):.2f}")
    print(f"  Mean χ²/N = {np.mean(all_chi2):.2f}")
    print(f"  Fraction < 3: {np.mean(np.array(all_chi2) < 3):.1%}")
    print(f"  Fraction < 2: {np.mean(np.array(all_chi2) < 2):.1%}")
    
    # Plot examples
    plot_morphology_examples(master_table, results, params_global, 
                           params_morph, lambda_norm)
    
    return results

def plot_morphology_examples(master_table, results, params_global, 
                            params_morph, lambda_norm):
    """
    Plot examples from each morphology category
    """
    # Get best example from each primary category
    categories_to_plot = ['dwarf', 'spiral', 'massive', 'gas_rich']
    examples = {}
    
    for cat in categories_to_plot:
        cat_results = [r for r in results if cat in r['categories']]
        if cat_results:
            cat_results.sort(key=lambda x: x['chi2_reduced'])
            examples[cat] = cat_results[0]
    
    n_examples = len(examples)
    fig, axes = plt.subplots(1, n_examples, figsize=(5*n_examples, 5))
    if n_examples == 1:
        axes = [axes]
        
    for ax, (cat, res) in zip(axes, examples.items()):
        galaxy = master_table[res['name']]
        
        r = galaxy['r']
        v_obs = galaxy['v_obs']
        df = galaxy['data']
        v_err = df['verr'].values
        v_gas = df['vgas'].values
        v_disk = df['vdisk'].values
        v_bul = df['vbul'].values
        
        # Calculate model
        w = morphology_weight(r, galaxy, params_global, params_morph)
        G_eff = G_kpc * lambda_norm * w
        
        ml = res['ml']
        v_disk_scaled = v_disk * np.sqrt(ml)
        v2_newton = v_gas**2 + v_disk_scaled**2 + v_bul**2
        g_newton = v2_newton / r
        g_eff = g_newton * (G_eff / G_kpc)
        v_model = np.sqrt(g_eff * r)
        
        # Plot
        ax.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=3,
                   alpha=0.6, label='Data')
        ax.plot(r, v_model, 'r-', linewidth=2,
               label=f'Model (M/L={ml:.1f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{cat.upper()}: {res["name"]}\n'
                    f'χ²/N={res["chi2_reduced"]:.2f}')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
    plt.tight_layout()
    plt.savefig('ledger_morphology_examples.png', dpi=150)
    print("Saved: ledger_morphology_examples.png")

def main():
    """Main execution"""
    
    # Load master table
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
        
    print(f"Loaded {len(master_table)} galaxies")
    
    # Optimize parameters
    params_opt = optimize_morphology_params(master_table, n_galaxies=40)
    
    print("\n" + "="*60)
    print("OPTIMIZED PARAMETERS:")
    print("="*60)
    print("Global parameters:")
    print(f"  α = {params_opt[0]:.3f} (time scaling)")
    print(f"  C₀ = {params_opt[1]:.3f} (gas complexity base)")
    print(f"  γ = {params_opt[2]:.3f} (gas exponent)")
    print(f"  δ = {params_opt[3]:.3f} (surface brightness)")
    
    print("\nMorphology adjustments:")
    print(f"  Dwarf: α_adj={params_opt[4]:.3f}, C₀_adj={params_opt[5]:.3f}, "
          f"r₁_scale={params_opt[6]:.3f}")
    print(f"  Massive: α_adj={params_opt[7]:.3f}, n₁_scale={params_opt[8]:.3f}")
    print(f"  Gas-rich: C₀_adj={params_opt[9]:.3f}, n₂_scale={params_opt[10]:.3f}")
    print(f"  LSB: n₁_scale={params_opt[11]:.3f}, n₂_scale={params_opt[12]:.3f}")
    print("="*60)
    
    # Analyze full sample
    results = analyze_morphology_results(master_table, params_opt)
    
    # Save
    output = {
        'params_opt': params_opt,
        'results': results
    }
    
    with open('ledger_morphology_results.pkl', 'wb') as f:
        pickle.dump(output, f)
        
    print("\nSaved: ledger_morphology_results.pkl")

if __name__ == "__main__":
    main() 