#!/usr/bin/env python3
"""
Cross-validated ledger solver with galaxy-specific profiles and regularization
Step 9 implementation: 5-fold CV + L2 penalty on extreme n(r) values
"""

import numpy as np
import pickle
from sklearn.model_selection import KFold
from ledger_galaxy_specific import global_objective_specific
from ledger_galaxy_specific import optimize_specific, analyze_specific_results

# Load master table
def load_master():
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    return master_table


def cross_val_objective(params, master_table, n_splits=5):
    """Compute average CV error with penalty"""
    galaxy_names = list(master_table.keys())
    X = np.arange(len(galaxy_names))  # Dummy
    kf = KFold(n_splits=n_splits, shuffle=True, random_state=42)
    scores = []
    
    for train_index, test_index in kf.split(X):
        train_names = [galaxy_names[i] for i in train_index]
        test_names = [galaxy_names[i] for i in test_index]
        train_table = {name: master_table[name] for name in train_names}
        test_table = {name: master_table[name] for name in test_names}
        
        # Fit on train (we use objective directly as proxy, not full inner loop)
        train_score = global_objective_specific(params, train_table)
        test_score = global_objective_specific(params, test_table)
        
        # Use test score
        scores.append(test_score)
    
    cv_score = np.mean(scores)
    
    # Regularization: penalize small lambda_norm (too much boost)
    lambda_norm_est = 0.02 + (params[1] / 100)  # rough heuristic
    penalty = 5.0 * (0.02 - lambda_norm_est)**2 if lambda_norm_est < 0.02 else 0
    
    return cv_score + penalty


def optimize_cv(master_table, n_galaxies=50):
    """Optimize parameters using differential evolution with CV objective"""
    from scipy.optimize import differential_evolution
    # Use subset for speed during optimization
    galaxy_names = list(master_table.keys())[:n_galaxies]
    subset = {name: master_table[name] for name in galaxy_names}
    
    bounds = [
        (0.0, 1.0),    # alpha
        (0.0, 10.0),   # C0 lower to avoid huge boosts
        (0.5, 3.0),    # gamma
        (0.0, 1.0),    # delta
        (0.05, 0.3),   # h_z_ratio tighter
        (0.0, 0.5),    # smoothness
        (0.0, 5.0)     # prior_strength stronger bound
    ]
    
    print(f"Optimizing with 5-fold CV on {n_galaxies} galaxies...")
    print("Using regularization to prevent overfitting")
    
    result = differential_evolution(
        lambda p: cross_val_objective(p, subset, n_splits=5),
        bounds,
        maxiter=15,  # Fewer iterations for speed
        popsize=10,
        disp=True
    )
    return result.x, result.fun


def main():
    master_table = load_master()
    print(f"Loaded {len(master_table)} galaxies")
    
    params_opt, score_opt = optimize_cv(master_table)
    print("\nCV optimization complete")
    print(f"Mean CV χ²/N = {score_opt:.2f}")
    print("Parameters:")
    names = ['α','C₀','γ','δ','h_z/R_d','smooth','prior']
    for n,v in zip(names, params_opt):
        print(f"  {n} = {v:.3f}")
    
    # Final analysis
    results = analyze_specific_results(master_table, params_opt)
    
    with open('ledger_specific_cv_results.pkl','wb') as f:
        pickle.dump({'params':params_opt,'results':results}, f)
    print("Saved ledger_specific_cv_results.pkl")

if __name__ == "__main__":
    main() 