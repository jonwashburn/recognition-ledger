#!/usr/bin/env python3
"""
Calculate global bandwidth budget:
- Total recognition weight W_tot across all SPARC galaxies
- Newtonian baseline W_Newt
- Required normalization factor λ
"""

import numpy as np
import pickle

# Constants
tau_0 = 1e8  # Fundamental cycle time in years (placeholder)
Sigma_star = 1e8  # Normalizing surface brightness M_sun/kpc²

def recognition_weight(r, T_dyn, f_gas, Sigma_0, params):
    """
    Calculate recognition weight w(r) at each radius
    
    w(r) = ξ * n_raw(r)
    where:
    ξ = [1 + C0 * f_gas^γ * (Sigma_0/Sigma_*)^δ]
    n_raw = (T_dyn/tau_0)^α
    """
    alpha, C0, gamma, delta = params
    
    # Complexity factor
    xi = 1 + C0 * (f_gas ** gamma) * ((Sigma_0 / Sigma_star) ** delta)
    
    # Raw refresh interval (time-based)
    n_raw = (T_dyn / tau_0) ** alpha
    
    # Total weight
    w = xi * n_raw
    
    return w

def calculate_global_weights(master_table, params):
    """
    Calculate total recognition weight and Newtonian baseline
    for all galaxies in the master table
    """
    W_tot = 0
    W_Newt = 0
    n_points = 0
    
    for name, galaxy in master_table.items():
        # Get galaxy properties
        r = galaxy['r']  # kpc
        T_dyn = galaxy['T_dyn']  # years
        f_gas = galaxy['f_gas_true']
        Sigma_0 = galaxy['Sigma_0']
        
        # Calculate weights at each radius
        w = recognition_weight(r, T_dyn, f_gas, Sigma_0, params)
        
        # Sum up (using trapezoidal integration)
        if len(r) > 1:
            dr = np.diff(r)
            w_avg = 0.5 * (w[:-1] + w[1:])
            W_tot += np.sum(w_avg * dr)
            W_Newt += np.sum(dr)  # Just the radial extent
        
        n_points += len(r)
    
    # Calculate normalization factor
    rho = W_tot / W_Newt if W_Newt > 0 else 1.0
    
    return {
        'W_tot': W_tot,
        'W_Newt': W_Newt,
        'rho': rho,
        'n_points': n_points,
        'lambda': 1.0 / rho  # Normalization to make average boost = 1
    }

def analyze_weight_distribution(master_table, params):
    """
    Analyze how recognition weights are distributed across
    different galaxy types
    """
    weights_by_type = {
        'gas_poor': [],  # f_gas < 0.1
        'gas_moderate': [],  # 0.1 <= f_gas < 0.5
        'gas_rich': [],  # f_gas >= 0.5
        'high_SB': [],  # Sigma_0 > 1e9
        'low_SB': []   # Sigma_0 <= 1e9
    }
    
    for name, galaxy in master_table.items():
        r = galaxy['r']
        T_dyn = galaxy['T_dyn']
        f_gas = galaxy['f_gas_true']
        Sigma_0 = galaxy['Sigma_0']
        
        # Calculate mean weight for this galaxy
        w = recognition_weight(r, T_dyn, f_gas, Sigma_0, params)
        w_mean = np.mean(w)
        
        # Categorize
        if f_gas < 0.1:
            weights_by_type['gas_poor'].append(w_mean)
        elif f_gas < 0.5:
            weights_by_type['gas_moderate'].append(w_mean)
        else:
            weights_by_type['gas_rich'].append(w_mean)
            
        if Sigma_0 > 1e9:
            weights_by_type['high_SB'].append(w_mean)
        else:
            weights_by_type['low_SB'].append(w_mean)
    
    # Calculate statistics
    stats = {}
    for category, weights in weights_by_type.items():
        if weights:
            stats[category] = {
                'mean': np.mean(weights),
                'std': np.std(weights),
                'count': len(weights)
            }
    
    return stats

def main():
    """Calculate and display global bandwidth budget"""
    
    # Load master table
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    print(f"Loaded {len(master_table)} galaxies")
    
    # Test parameters (will be optimized later)
    params = [
        0.5,   # alpha: time scaling exponent
        2.0,   # C0: gas complexity amplitude
        1.5,   # gamma: gas fraction exponent
        0.3    # delta: surface brightness exponent
    ]
    
    print("\nCalculating global bandwidth budget...")
    print(f"Parameters: α={params[0]}, C₀={params[1]}, γ={params[2]}, δ={params[3]}")
    
    # Calculate global weights
    results = calculate_global_weights(master_table, params)
    
    print("\nGlobal bandwidth results:")
    print(f"  Total recognition weight W_tot = {results['W_tot']:.2e}")
    print(f"  Newtonian baseline W_Newt = {results['W_Newt']:.2e}")
    print(f"  Raw boost factor ρ = W_tot/W_Newt = {results['rho']:.3f}")
    print(f"  Normalization factor λ = 1/ρ = {results['lambda']:.3f}")
    print(f"  Total data points = {results['n_points']}")
    
    # Analyze distribution
    print("\nAnalyzing weight distribution by galaxy type...")
    stats = analyze_weight_distribution(master_table, params)
    
    print("\nMean recognition weights by category:")
    for category, stat in stats.items():
        print(f"  {category}: {stat['mean']:.3f} ± {stat['std']:.3f} (N={stat['count']})")
    
    # Save results
    output = {
        'params': params,
        'global_results': results,
        'category_stats': stats
    }
    
    with open('bandwidth_analysis.pkl', 'wb') as f:
        pickle.dump(output, f)
    
    print("\nSaved results to bandwidth_analysis.pkl")

if __name__ == "__main__":
    main() 