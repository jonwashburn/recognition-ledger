#!/usr/bin/env python3
"""
Test the Ledger-Refresh model with complexity factor ξ = 1 + C₀ f_gas^γ
on SPARC galaxies. We'll fit C₀ and γ globally across multiple galaxies.
"""

import numpy as np
import pandas as pd
import os
from scipy.optimize import minimize, minimize_scalar
import matplotlib.pyplot as plt

# Constants
G_kpc = 4.302e-6  # kpc (km/s)^2 / Msun
r1 = 0.97  # kpc
r2 = 24.3  # kpc


def n_raw(r_kpc):
    """Base refresh interval n(r) without complexity factor."""
    n = np.ones_like(r_kpc)
    mid = (r_kpc >= r1) & (r_kpc < r2)
    outer = r_kpc >= r2
    n[mid] = np.sqrt(r_kpc[mid] / r1)
    n[outer] = 6.0
    return n


def load_galaxy(path):
    """Load SPARC galaxy data and extract gas fraction."""
    df = pd.read_csv(
        path,
        sep=r"\s+",
        comment="#",
        names=["rad", "vobs", "verr", "vgas", "vdisk", "vbul", "sbdisk", "sbbul"],
    )
    df = df[(df["rad"] > 0) & (df["vobs"] > 0) & (df["verr"] > 0)].reset_index(drop=True)
    
    # Estimate gas fraction from velocity contributions
    # f_gas ≈ <v_gas²> / (<v_gas²> + <v_disk²> + <v_bul²>)
    v2_gas = np.mean(df["vgas"]**2)
    v2_disk = np.mean(df["vdisk"]**2)
    v2_bul = np.mean(df["vbul"]**2)
    v2_total = v2_gas + v2_disk + v2_bul
    
    f_gas = v2_gas / v2_total if v2_total > 0 else 0.0
    
    return df, f_gas


def model_velocity(r, v_gas, v_disk, v_bul, ml_disk, f_gas, C0, gamma):
    """Calculate model velocity with complexity-adjusted boost."""
    # Scale disk by M/L
    v_disk_scaled = v_disk * np.sqrt(ml_disk)
    v_newton_sq = v_gas**2 + v_disk_scaled**2 + v_bul**2
    g_newton = v_newton_sq / r
    
    # Complexity factor
    xi = 1 + C0 * f_gas**gamma
    
    # Total boost
    n_eff = xi * n_raw(r)
    g_eff = g_newton * n_eff
    
    return np.sqrt(g_eff * r)


def fit_single_galaxy(df, f_gas, C0, gamma):
    """Fit M/L for a single galaxy given global C0, gamma."""
    r = df["rad"].values
    v_obs = df["vobs"].values
    v_err = df["verr"].values
    v_gas = df["vgas"].values
    v_disk = df["vdisk"].values
    v_bul = df["vbul"].values
    
    def chi2(ml):
        v_model = model_velocity(r, v_gas, v_disk, v_bul, ml, f_gas, C0, gamma)
        return np.sum(((v_obs - v_model) / v_err)**2)
    
    res = minimize_scalar(chi2, bounds=(0.1, 5.0), method="bounded")
    return res.x, res.fun / len(df)


def global_chi2(params, galaxy_data):
    """Total chi² across all galaxies for given C0, gamma."""
    C0, gamma = params
    if C0 < 0 or gamma < 0 or gamma > 3:
        return 1e10  # Penalty for unphysical values
    
    total_chi2 = 0
    n_points = 0
    
    for name, (df, f_gas) in galaxy_data.items():
        ml, chi2_n = fit_single_galaxy(df, f_gas, C0, gamma)
        total_chi2 += chi2_n * len(df)
        n_points += len(df)
    
    return total_chi2 / n_points


def main():
    # Load sample galaxies
    sample_files = [
        "Rotmod_LTG/NGC2403_rotmod.dat",
        "Rotmod_LTG/NGC3198_rotmod.dat",
        "Rotmod_LTG/DDO154_rotmod.dat",
        "Rotmod_LTG/NGC6503_rotmod.dat",
        "Rotmod_LTG/UGC02885_rotmod.dat",
        "Rotmod_LTG/NGC2841_rotmod.dat",
        "Rotmod_LTG/NGC0300_rotmod.dat",
        "Rotmod_LTG/UGC05999_rotmod.dat",
    ]
    
    # Load data
    galaxy_data = {}
    for path in sample_files:
        if os.path.exists(path):
            name = os.path.basename(path).replace("_rotmod.dat", "")
            try:
                df, f_gas = load_galaxy(path)
                galaxy_data[name] = (df, f_gas)
                print(f"Loaded {name}: f_gas = {f_gas:.3f}, N_points = {len(df)}")
            except Exception as e:
                print(f"Error loading {name}: {e}")
    
    if not galaxy_data:
        print("No galaxies loaded!")
        return
    
    print("\n" + "="*60)
    print("FITTING GLOBAL COMPLEXITY PARAMETERS C₀ and γ")
    print("="*60)
    
    # Optimize C0 and gamma
    result = minimize(
        lambda p: global_chi2(p, galaxy_data),
        x0=[5.0, 1.0],  # Initial guess
        bounds=[(0, 20), (0.5, 2.5)],
        method='L-BFGS-B'
    )
    
    C0_best, gamma_best = result.x
    
    print(f"\nBest-fit parameters:")
    print(f"  C₀ = {C0_best:.2f}")
    print(f"  γ = {gamma_best:.2f}")
    print(f"  Global χ²/N = {result.fun:.2f}")
    
    # Show individual galaxy fits
    print("\nIndividual galaxy results:")
    print("-"*60)
    print(f"{'Galaxy':<12} {'f_gas':>6} {'ξ':>6} {'M/L':>6} {'χ²/N':>8}")
    print("-"*60)
    
    chi2_values = []
    for name, (df, f_gas) in galaxy_data.items():
        ml, chi2_n = fit_single_galaxy(df, f_gas, C0_best, gamma_best)
        xi = 1 + C0_best * f_gas**gamma_best
        chi2_values.append(chi2_n)
        print(f"{name:<12} {f_gas:>6.3f} {xi:>6.2f} {ml:>6.2f} {chi2_n:>8.1f}")
    
    print("-"*60)
    print(f"Median χ²/N = {np.median(chi2_values):.1f}")
    print(f"Mean χ²/N = {np.mean(chi2_values):.1f}")
    
    # Plot example fits
    plot_examples(galaxy_data, C0_best, gamma_best)


def plot_examples(galaxy_data, C0, gamma):
    """Plot a few example galaxy fits."""
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    axes = axes.flatten()
    
    for idx, (name, (df, f_gas)) in enumerate(list(galaxy_data.items())[:4]):
        ax = axes[idx]
        
        # Fit M/L
        ml, chi2_n = fit_single_galaxy(df, f_gas, C0, gamma)
        xi = 1 + C0 * f_gas**gamma
        
        # Get data
        r = df["rad"].values
        v_obs = df["vobs"].values
        v_err = df["verr"].values
        v_gas = df["vgas"].values
        v_disk = df["vdisk"].values
        v_bul = df["vbul"].values
        
        # Model
        v_model = model_velocity(r, v_gas, v_disk, v_bul, ml, f_gas, C0, gamma)
        
        # Plot
        ax.errorbar(r, v_obs, yerr=v_err, fmt='ko', markersize=4, alpha=0.7, label='Data')
        ax.plot(r, v_model, 'r-', linewidth=2, label=f'Model (ξ={xi:.1f})')
        
        # Mark recognition scales
        ax.axvline(r1, color='green', linestyle=':', alpha=0.5)
        ax.axvline(r2, color='blue', linestyle=':', alpha=0.5)
        
        ax.set_xlabel('Radius [kpc]')
        ax.set_ylabel('Velocity [km/s]')
        ax.set_title(f'{name}: χ²/N={chi2_n:.1f}, f_gas={f_gas:.2f}')
        ax.legend()
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('ledger_complexity_fits.png', dpi=150)
    print(f"\nSaved: ledger_complexity_fits.png")


if __name__ == "__main__":
    main() 