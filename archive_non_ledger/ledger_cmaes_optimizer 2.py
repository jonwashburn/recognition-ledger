#!/usr/bin/env python3
"""
CMA-ES optimizer for ledger gravity model (Step 8)
Covariance Matrix Adaptation Evolution Strategy - faster and more robust
"""

import numpy as np
import pickle
from scipy.optimize import minimize
import warnings
warnings.filterwarnings('ignore')

# Import objective functions from other modules
from ledger_full_error_model import global_objective_full_error
from ledger_galaxy_specific import global_objective_specific

class CMAES:
    """Simple CMA-ES implementation"""
    
    def __init__(self, x0, sigma0, bounds=None, popsize=None):
        self.dim = len(x0)
        self.xmean = np.array(x0)
        self.sigma = sigma0
        self.bounds = bounds
        
        # Population size
        self.popsize = popsize or 4 + int(3 * np.log(self.dim))
        self.mu = self.popsize // 2
        
        # Weights
        self.weights = np.log(self.mu + 0.5) - np.log(np.arange(1, self.mu + 1))
        self.weights /= np.sum(self.weights)
        self.mueff = 1 / np.sum(self.weights**2)
        
        # Adaptation constants
        self.cc = (4 + self.mueff/self.dim) / (self.dim + 4 + 2*self.mueff/self.dim)
        self.cs = (self.mueff + 2) / (self.dim + self.mueff + 5)
        self.c1 = 2 / ((self.dim + 1.3)**2 + self.mueff)
        self.cmu = min(1 - self.c1, 2 * (self.mueff - 2 + 1/self.mueff) / ((self.dim + 2)**2 + self.mueff))
        self.damps = 1 + 2*max(0, np.sqrt((self.mueff-1)/(self.dim+1))-1) + self.cs
        
        # Initialize dynamic strategy parameters
        self.pc = np.zeros(self.dim)
        self.ps = np.zeros(self.dim)
        self.C = np.eye(self.dim)
        self.invsqrtC = np.eye(self.dim)
        self.eigeneval = 0
        self.chiN = np.sqrt(self.dim) * (1 - 1/(4*self.dim) + 1/(21*self.dim**2))
        
    def sample(self):
        """Sample new population"""
        if self.eigeneval % (self.popsize // (self.c1 + self.cmu) // self.dim // 10) == 0:
            self.eigeneval = 0
            self.C = np.triu(self.C) + np.triu(self.C, 1).T
            D, B = np.linalg.eigh(self.C)
            D = np.sqrt(D)
            self.invsqrtC = B @ np.diag(1/D) @ B.T
            
        # Sample
        arz = np.random.randn(self.popsize, self.dim)
        arx = self.xmean + self.sigma * (arz @ np.diag(np.sqrt(np.diag(self.C))))
        
        # Apply bounds
        if self.bounds is not None:
            for i in range(self.popsize):
                for j in range(self.dim):
                    arx[i, j] = np.clip(arx[i, j], self.bounds[j][0], self.bounds[j][1])
        
        return arx, arz
    
    def update(self, arx, arz, arfitness):
        """Update distribution parameters"""
        # Sort by fitness
        arindex = np.argsort(arfitness)
        
        # New mean
        xold = self.xmean
        self.xmean = np.dot(self.weights, arx[arindex[:self.mu]])
        
        # Cumulation for sigma
        self.ps = (1 - self.cs) * self.ps + np.sqrt(self.cs * (2 - self.cs) * self.mueff) * self.invsqrtC @ (self.xmean - xold) / self.sigma
        hsig = np.linalg.norm(self.ps) / np.sqrt(1-(1-self.cs)**(2*(self.eigeneval+1))) < (1.4 + 2/(self.dim+1)) * self.chiN
        
        # Cumulation for C
        self.pc = (1 - self.cc) * self.pc + hsig * np.sqrt(self.cc * (2 - self.cc) * self.mueff) * (self.xmean - xold) / self.sigma
        
        # Update C
        artmp = (arx[arindex[:self.mu]] - xold) / self.sigma
        self.C = (1 - self.c1 - self.cmu) * self.C + \
                 self.c1 * (np.outer(self.pc, self.pc) + (1-hsig) * self.cc * (2-self.cc) * self.C) + \
                 self.cmu * artmp.T @ np.diag(self.weights) @ artmp
        
        # Update sigma
        self.sigma *= np.exp((self.cs / self.damps) * (np.linalg.norm(self.ps) / self.chiN - 1))
        
        self.eigeneval += 1

def optimize_cmaes(objective_func, x0, bounds, master_table, maxiter=50):
    """
    Optimize using CMA-ES
    """
    print("Optimizing with CMA-ES (Covariance Matrix Adaptation)")
    print(f"Starting from: {x0}")
    print(f"Bounds: {bounds}")
    
    # Initialize CMA-ES
    sigma0 = 0.3  # Initial step size
    cmaes = CMAES(x0, sigma0, bounds)
    
    best_fitness = np.inf
    best_x = x0
    history = []
    
    for generation in range(maxiter):
        # Sample population
        arx, arz = cmaes.sample()
        
        # Evaluate fitness
        arfitness = []
        for x in arx:
            try:
                fitness = objective_func(x, master_table)
                arfitness.append(fitness)
            except:
                arfitness.append(1e10)
        
        arfitness = np.array(arfitness)
        
        # Update best
        min_idx = np.argmin(arfitness)
        if arfitness[min_idx] < best_fitness:
            best_fitness = arfitness[min_idx]
            best_x = arx[min_idx].copy()
        
        # Update CMA-ES
        cmaes.update(arx, arz, arfitness)
        
        # Print progress
        if generation % 5 == 0:
            print(f"Generation {generation}: best χ²/N = {best_fitness:.3f}, "
                  f"mean = {np.mean(arfitness):.3f}, σ = {cmaes.sigma:.4f}")
        
        history.append({
            'generation': generation,
            'best': best_fitness,
            'mean': np.mean(arfitness),
            'std': np.std(arfitness),
            'sigma': cmaes.sigma
        })
        
        # Convergence check
        if cmaes.sigma < 1e-8:
            print("Converged (sigma too small)")
            break
    
    return best_x, best_fitness, history

def main():
    """Compare CMA-ES with differential evolution"""
    
    print("Loading master table...")
    with open('sparc_master.pkl', 'rb') as f:
        master_table = pickle.load(f)
    
    # Use subset for testing
    n_test = 30
    galaxy_names = list(master_table.keys())[:n_test]
    subset = {name: master_table[name] for name in galaxy_names}
    
    print(f"\nTesting CMA-ES on {n_test} galaxies")
    
    # Parameters for full error model
    bounds = [
        (0.0, 1.0),    # alpha
        (0.0, 15.0),   # C0
        (0.5, 3.0),    # gamma
        (0.0, 1.0),    # delta
        (0.05, 0.5),   # h_z_ratio
        (0.0, 0.3),    # smoothness
        (0.0, 5.0),    # prior_strength
        (0.0, 1.0),    # alpha_beam
        (0.0, 0.5)     # beta_asym
    ]
    
    # Initial guess (from previous results)
    x0 = [0.5, 5.0, 1.8, 0.7, 0.3, 0.1, 1.0, 0.3, 0.1]
    
    # Run CMA-ES
    print("\n" + "="*60)
    print("Running CMA-ES optimization")
    print("="*60)
    
    best_x, best_fitness, history = optimize_cmaes(
        global_objective_full_error, x0, bounds, subset, maxiter=30
    )
    
    print("\n" + "="*60)
    print("CMA-ES RESULTS")
    print("="*60)
    print(f"Best χ²/N = {best_fitness:.3f}")
    print("Best parameters:")
    param_names = ['α', 'C₀', 'γ', 'δ', 'h_z/R_d', 'smooth', 'prior', 'α_beam', 'β_asym']
    for name, val in zip(param_names, best_x):
        print(f"  {name} = {val:.3f}")
    
    # Save results
    output = {
        'best_x': best_x,
        'best_fitness': best_fitness,
        'history': history,
        'method': 'CMA-ES'
    }
    
    with open('ledger_cmaes_results.pkl', 'wb') as f:
        pickle.dump(output, f)
    
    print("\nSaved results to ledger_cmaes_results.pkl")
    
    # Plot convergence
    import matplotlib.pyplot as plt
    
    generations = [h['generation'] for h in history]
    best_values = [h['best'] for h in history]
    mean_values = [h['mean'] for h in history]
    
    plt.figure(figsize=(10, 6))
    plt.plot(generations, best_values, 'r-', linewidth=2, label='Best')
    plt.plot(generations, mean_values, 'b--', alpha=0.7, label='Population mean')
    plt.xlabel('Generation')
    plt.ylabel('χ²/N')
    plt.title('CMA-ES Convergence')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.yscale('log')
    plt.tight_layout()
    plt.savefig('cmaes_convergence.png', dpi=150)
    print("Saved convergence plot: cmaes_convergence.png")

if __name__ == "__main__":
    main() 