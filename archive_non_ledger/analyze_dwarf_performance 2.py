#!/usr/bin/env python3
"""
Analyze dwarf galaxy performance with bandwidth triage model
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import differential_evolution
import json
from lnal_bandwidth_triage_model import load_sparc_data, fit_galaxy, recognition_weight, calculate_model_velocity

def identify_dwarf_galaxies(sparc_data):
    """Identify dwarf galaxies based on velocity and name patterns"""
    dwarfs = []
    
    for galaxy_name, galaxy_data in sparc_data.items():
        curve = galaxy_data['curve']
        v_max = np.max(curve['V_obs'])
        
        # Criteria for dwarf galaxies:
        # 1. Name contains DDO, D, UGC with low numbers, or other dwarf indicators
        # 2. Low maximum velocity (< 100 km/s typically)
        is_dwarf_name = any(prefix in galaxy_name for prefix in ['DDO', 'UGCA', 'CVnIdwA', 'WLM'])
        is_d_galaxy = galaxy_name.startswith('D') and galaxy_name[1:].split('-')[0].isdigit()
        is_low_velocity = v_max < 100
        
        if is_dwarf_name or (is_d_galaxy and is_low_velocity) or v_max < 80:
            dwarfs.append(galaxy_name)
            
    return sorted(dwarfs)

def optimize_for_dwarfs(sparc_data, dwarf_names):
    """Optimize parameters specifically for dwarf galaxies"""
    
    print(f"Optimizing on {len(dwarf_names)} dwarf galaxies:")
    for name in dwarf_names[:10]:  # Show first 10
        print(f"  - {name}")
    if len(dwarf_names) > 10:
        print(f"  ... and {len(dwarf_names)-10} more")
    
    # Global optimization function for dwarfs only
    def dwarf_chi2(param_array):
        params = {
            'alpha': param_array[0],
            'C0': param_array[1],
            'gamma': param_array[2],
            'delta': param_array[3],
            'lambda_norm': param_array[4]
        }
        
        total_chi2 = 0
        total_n = 0
        
        for galaxy_name in dwarf_names:
            if galaxy_name not in sparc_data:
                continue
                
            result = fit_galaxy(galaxy_name, sparc_data[galaxy_name], params)
            if result is not None:
                total_chi2 += result['chi2']
                total_n += len(result['r_kpc'])
        
        return total_chi2 / total_n if total_n > 0 else 1e10
    
    # Parameter bounds - adjusted for dwarfs
    bounds = [
        (0.1, 0.5),    # alpha: time scaling exponent
        (0.1, 20.0),   # C0: complexity amplitude (wider range for dwarfs)
        (0.5, 5.0),    # gamma: gas fraction power
        (0.1, 2.0),    # delta: surface brightness power
        (0.01, 2.0)    # lambda_norm: global normalization
    ]
    
    print("\nRunning optimization for dwarf galaxies...")
    result = differential_evolution(dwarf_chi2, bounds, seed=42, 
                                  maxiter=100, popsize=15, disp=True)
    
    # Extract optimal parameters
    dwarf_params = {
        'alpha': result.x[0],
        'C0': result.x[1],
        'gamma': result.x[2],
        'delta': result.x[3],
        'lambda_norm': result.x[4]
    }
    
    print("\nOptimal parameters for dwarf galaxies:")
    for k, v in dwarf_params.items():
        print(f"  {k}: {v:.3f}")
    
    return dwarf_params

def analyze_all_galaxies_by_type(sparc_data, params):
    """Analyze performance on all galaxies, categorized by type"""
    
    dwarf_results = []
    spiral_results = []
    all_results = []
    
    # Get dwarf galaxy names
    dwarf_names = identify_dwarf_galaxies(sparc_data)
    
    print(f"\nAnalyzing {len(sparc_data)} galaxies...")
    print(f"  - {len(dwarf_names)} dwarf galaxies")
    print(f"  - {len(sparc_data) - len(dwarf_names)} spiral/other galaxies")
    
    for i, (galaxy_name, galaxy_data) in enumerate(sparc_data.items()):
        if i % 30 == 0:
            print(f"  Progress: {i}/{len(sparc_data)}")
            
        result = fit_galaxy(galaxy_name, galaxy_data, params)
        if result is not None:
            chi2_N = result['chi2_reduced']
            all_results.append(chi2_N)
            
            if galaxy_name in dwarf_names:
                dwarf_results.append(chi2_N)
            else:
                spiral_results.append(chi2_N)
    
    # Convert to arrays
    all_results = np.array(all_results)
    dwarf_results = np.array(dwarf_results)
    spiral_results = np.array(spiral_results)
    
    # Statistics
    print("\n" + "="*70)
    print("PERFORMANCE BY GALAXY TYPE")
    print("="*70)
    
    print(f"\nDWARF GALAXIES ({len(dwarf_results)} galaxies):")
    print(f"  Median χ²/N: {np.median(dwarf_results):.3f}")
    print(f"  Mean χ²/N: {np.mean(dwarf_results):.3f}")
    print(f"  Best χ²/N: {np.min(dwarf_results):.3f}")
    print(f"  Worst χ²/N: {np.max(dwarf_results):.3f}")
    print(f"  Fraction < 0.5: {np.sum(dwarf_results < 0.5)/len(dwarf_results)*100:.1f}%")
    print(f"  Fraction < 1.0: {np.sum(dwarf_results < 1.0)/len(dwarf_results)*100:.1f}%")
    
    print(f"\nSPIRAL/OTHER GALAXIES ({len(spiral_results)} galaxies):")
    print(f"  Median χ²/N: {np.median(spiral_results):.3f}")
    print(f"  Mean χ²/N: {np.mean(spiral_results):.3f}")
    print(f"  Best χ²/N: {np.min(spiral_results):.3f}")
    print(f"  Worst χ²/N: {np.max(spiral_results):.3f}")
    print(f"  Fraction < 1.0: {np.sum(spiral_results < 1.0)/len(spiral_results)*100:.1f}%")
    print(f"  Fraction < 2.0: {np.sum(spiral_results < 2.0)/len(spiral_results)*100:.1f}%")
    
    print(f"\nALL GALAXIES ({len(all_results)} galaxies):")
    print(f"  Median χ²/N: {np.median(all_results):.3f}")
    print(f"  Mean χ²/N: {np.mean(all_results):.3f}")
    
    return {
        'dwarf_results': dwarf_results,
        'spiral_results': spiral_results,
        'all_results': all_results,
        'dwarf_names': dwarf_names
    }

def plot_dwarf_examples(sparc_data, dwarf_names, params):
    """Plot example dwarf galaxy fits"""
    
    # Select best-fitting dwarfs
    dwarf_chi2 = []
    for name in dwarf_names:
        if name in sparc_data:
            result = fit_galaxy(name, sparc_data[name], params)
            if result is not None:
                dwarf_chi2.append((name, result['chi2_reduced'], result))
    
    # Sort by chi2 and take best 6
    dwarf_chi2.sort(key=lambda x: x[1])
    best_dwarfs = dwarf_chi2[:6]
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    for idx, (galaxy_name, chi2_N, result) in enumerate(best_dwarfs):
        ax = axes[idx]
        
        r_kpc = result['r_kpc']
        v_obs = result['v_obs']
        v_err = result['v_err']
        v_baryon = result['v_baryon']
        v_model = result['v_model']
        
        # Plot
        ax.errorbar(r_kpc, v_obs, yerr=v_err, fmt='ko', markersize=4, 
                   label='Observed', alpha=0.7)
        ax.plot(r_kpc, v_baryon, 'b--', linewidth=2, 
               label='Baryons (Newton)', alpha=0.7)
        ax.plot(r_kpc, v_model, 'r-', linewidth=2.5,
               label=f'LNAL (χ²/N={chi2_N:.2f})')
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{galaxy_name}')
        ax.legend(loc='lower right')
        ax.grid(True, alpha=0.3)
        ax.set_xlim(0, None)
        ax.set_ylim(0, None)
    
    plt.suptitle('Best-Fitting Dwarf Galaxies with Bandwidth Triage Model', fontsize=14)
    plt.tight_layout()
    plt.savefig('dwarf_galaxy_fits.png', dpi=150)
    print("\nSaved: dwarf_galaxy_fits.png")

def main():
    # Load data
    print("Loading SPARC data from Rotmod_LTG...")
    sparc_data = load_sparc_data()
    
    # Identify dwarf galaxies
    dwarf_names = identify_dwarf_galaxies(sparc_data)
    
    # First try with paper parameters
    print("\n" + "="*70)
    print("Testing paper parameters on dwarf galaxies")
    print("="*70)
    
    paper_params = {
        'alpha': 0.194,
        'C0': 5.064,
        'gamma': 2.953,
        'delta': 0.216,
        'lambda_norm': 0.119
    }
    
    results_paper = analyze_all_galaxies_by_type(sparc_data, paper_params)
    
    # Now optimize specifically for dwarfs
    print("\n" + "="*70)
    print("Optimizing specifically for dwarf galaxies")
    print("="*70)
    
    dwarf_optimized_params = optimize_for_dwarfs(sparc_data, dwarf_names)
    
    # Analyze with dwarf-optimized parameters
    print("\n" + "="*70)
    print("Testing dwarf-optimized parameters on all galaxies")
    print("="*70)
    
    results_optimized = analyze_all_galaxies_by_type(sparc_data, dwarf_optimized_params)
    
    # Plot examples
    plot_dwarf_examples(sparc_data, dwarf_names, dwarf_optimized_params)
    
    # Save results
    summary = {
        'paper_params': paper_params,
        'paper_dwarf_median': float(np.median(results_paper['dwarf_results'])),
        'paper_all_median': float(np.median(results_paper['all_results'])),
        'dwarf_optimized_params': dwarf_optimized_params,
        'optimized_dwarf_median': float(np.median(results_optimized['dwarf_results'])),
        'optimized_all_median': float(np.median(results_optimized['all_results'])),
        'n_dwarfs': len(dwarf_names),
        'dwarf_names': dwarf_names
    }
    
    with open('dwarf_analysis_results.json', 'w') as f:
        json.dump(summary, f, indent=2)
    
    print("\nResults saved to dwarf_analysis_results.json")
    
    # Check if we achieved the paper's claimed performance
    if np.median(results_optimized['dwarf_results']) < 0.2:
        print(f"\n✓ Achieved excellent dwarf performance: median χ²/N = {np.median(results_optimized['dwarf_results']):.3f}")
    
if __name__ == "__main__":
    main() 