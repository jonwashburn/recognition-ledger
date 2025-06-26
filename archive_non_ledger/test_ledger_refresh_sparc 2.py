#!/usr/bin/env python3
"""
Test the Ledger-Refresh gravity model (scale-dependent boost n(r))
on a handful of SPARC galaxies with a single fitted disk M/L ratio.

Boost factor (piece-wise):
  n(r)=1                       for r < r1  (Newtonian)
  n(r)=(r/r1)^{1/2}            for r1 <= r < r2 (mild boost)
  n(r)=6                       for r >= r2 (cosmic boost)
"""

import numpy as np
import pandas as pd
import os
from scipy.optimize import minimize_scalar
import matplotlib.pyplot as plt

# Constants
G_kpc = 4.302e-6  # kpc (km/s)^2 / Msun
r1 = 0.97  # kpc
r2 = 24.3  # kpc


def boost_factor(r_kpc: np.ndarray) -> np.ndarray:
    """Piecewise n(r) as defined above."""
    n = np.ones_like(r_kpc)
    mid = (r_kpc >= r1) & (r_kpc < r2)
    outer = r_kpc >= r2
    n[mid] = np.sqrt(r_kpc[mid] / r1)
    n[outer] = 6.0
    return n


def load_galaxy(path: str):
    """Load SPARC rotmod file into dataframe."""
    df = pd.read_csv(
        path,
        sep=r"\s+",
        comment="#",
        names=[
            "rad",
            "vobs",
            "verr",
            "vgas",
            "vdisk",
            "vbul",
            "sbdisk",
            "sbbul",
        ],
    )
    df = df[(df["rad"] > 0) & (df["vobs"] > 0) & (df["verr"] > 0)].reset_index(drop=True)
    return df


def fit_ml_ratio(df):
    """Fit disk mass-to-light ratio for best chi2 using ledger model."""
    r = df["rad"].values  # kpc
    v_obs = df["vobs"].values
    v_err = df["verr"].values
    v_gas = df["vgas"].values
    v_disk_base = df["vdisk"].values  # M/L=1
    v_bul = df["vbul"].values

    def chi2(ml):
        v_disk = v_disk_base * np.sqrt(ml)
        v_newton_sq = v_gas ** 2 + v_disk ** 2 + v_bul ** 2
        g_newton = v_newton_sq / r  # (km/s)^2/kpc
        n_r = boost_factor(r)
        g_eff = g_newton * n_r
        v_model = np.sqrt(g_eff * r)
        return np.sum(((v_obs - v_model) / v_err) ** 2)

    res = minimize_scalar(chi2, bounds=(0.1, 5.0), method="bounded")
    ml_best = res.x
    chi2_red = res.fun / len(df)
    return ml_best, chi2_red


def analyse_galaxies(files):
    results = []
    for path in files:
        name = os.path.basename(path).replace("_rotmod.dat", "")
        try:
            df = load_galaxy(path)
            ml, chi2_n = fit_ml_ratio(df)
            results.append((name, ml, chi2_n))
            print(f"{name:<12} M/L={ml:.2f}  chi2/N={chi2_n:.1f}")
        except Exception as e:
            print(f"{name:<12} ERROR {e}")
    return results


def main():
    sample_files = [
        "Rotmod_LTG/NGC2403_rotmod.dat",
        "Rotmod_LTG/NGC3198_rotmod.dat",
        "Rotmod_LTG/DDO154_rotmod.dat",
        "Rotmod_LTG/NGC6503_rotmod.dat",
        "Rotmod_LTG/UGC02885_rotmod.dat",
    ]
    sample_files = [f for f in sample_files if os.path.exists(f)]
    print("Ledger-Refresh Model on SPARC sample")
    print("=" * 50)
    results = analyse_galaxies(sample_files)
    if results:
        chi2_vals = np.array([x[2] for x in results])
        print("\nSUMMARY")
        print("Median chi2/N = {:.1f}".format(np.median(chi2_vals)))
        print("Mean   chi2/N = {:.1f}".format(np.mean(chi2_vals)))


if __name__ == "__main__":
    main() 