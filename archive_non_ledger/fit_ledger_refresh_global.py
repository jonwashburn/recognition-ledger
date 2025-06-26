#!/usr/bin/env python3
"""
Global 6-parameter optimisation of the Ledger-Refresh gravity model
Parameters optimised (p):
  p0 = α    : mid-range slope exponent          (0 < α < 1)
  p1 = n₂   : asymptotic boost (cosmic)         (3 < n₂ < 10)
  p2 = r₁   : inner transition radius  [kpc]    (0.3 < r₁ < 3)
  p3 = r₂   : outer transition radius [kpc]     (10 < r₂ < 50)
  p4 = C₀   : complexity amplitude              (0 < C₀ < 20)
  p5 = γ    : complexity exponent               (0 < γ < 3)
For each parameter set the script fits one stellar M/L per galaxy (inner loop)
and returns the global reduced χ².
"""
import numpy as np, pandas as pd, os, sys, json
from pathlib import Path
from scipy.optimize import minimize, minimize_scalar

# ---------- SPARC loader ------------------------------------------------ #

def load_rotmod(path: str):
    cols = ["rad","vobs","verr","vgas","vdisk","vbul","sbdisk","sbbul"]
    df = pd.read_csv(path, sep=r"\s+", comment="#", names=cols)
    df = df[(df["rad"]>0)&(df["vobs"]>0)&(df["verr"]>0)].reset_index(drop=True)
    # gas fraction proxy
    v2 = df[["vgas","vdisk","vbul"]]**2
    v_tot = v2.sum(axis=1).mean()
    f_gas = v2["vgas"].mean()/v_tot if v_tot>0 else 0
    return df, f_gas

# ---------- Model definition ------------------------------------------- #

def n_raw(r, alpha, n2, r1, r2):
    """Refresh interval without complexity."""
    r = np.asarray(r)
    n = np.ones_like(r)
    mid = (r>=r1)&(r<r2)
    outer = r>=r2
    n[mid] = (r[mid]/r1)**alpha
    n[outer] = n2
    return n

def velocity_model(df, ml, f_gas, params):
    alpha,n2,r1,r2,C0,gamma = params
    r = df["rad"].values
    v_gas = df["vgas"].values
    v_disk = df["vdisk"].values*np.sqrt(ml)
    v_bul = df["vbul"].values
    vN2 = v_gas**2+v_disk**2+v_bul**2
    gN = vN2/r
    xi = 1 + C0*(f_gas**gamma)
    g_eff = gN * xi * n_raw(r,alpha,n2,r1,r2)
    return np.sqrt(g_eff*r)

# ---------- χ² helpers -------------------------------------------------- #

def best_ml_for_gal(df,f_gas,params):
    v_obs = df["vobs"].values; v_err=df["verr"].values
    def chi2(ml):
        v_mod = velocity_model(df,ml,f_gas,params)
        return np.sum(((v_obs-v_mod)/v_err)**2)
    res=minimize_scalar(chi2,bounds=(0.1,5.0),method="bounded")
    return res.x, res.fun/len(df)

# ---------- Global objective ------------------------------------------- #

def global_chi2(p, gal_data):
    alpha,n2,r1,r2,C0,gamma = p
    # enforce bounds manually (L-BFGS itself respects bounds but inner calls might wander)
    if not(0<alpha<1 and 3<n2<10 and 0.3<r1<3 and 10<r2<50 and 0<C0<20 and 0<gamma<3 and r1<r2):
        return 1e9
    tot=0;npt=0
    for df,f_gas in gal_data.values():
        ml, chi = best_ml_for_gal(df,f_gas,p)
        tot += chi*len(df)
        npt += len(df)
    return tot/npt

# ---------- Main -------------------------------------------------------- #

def main():
    # sample list (use many)
    rotmod_dir = Path("Rotmod_LTG")
    files = sorted(rotmod_dir.glob("*_rotmod.dat"))[:30]  # first 30 galaxies for speed
    gal_data={}
    for f in files:
        df, fg = load_rotmod(str(f))
        gal_data[f.stem.replace("_rotmod","")]=(df,fg)
    if not gal_data:
        print("No data loaded"); sys.exit()
    print(f"Loaded {len(gal_data)} galaxies for optimisation")

    # initial guess
    p0=[0.5,6.0,0.97,24.3,3.6,1.5]
    bounds=[(0.1,0.9),(3,10),(0.3,3),(10,50),(0,20),(0.5,2.5)]
    result=minimize(lambda x: global_chi2(x,gal_data), p0, bounds=bounds, method='L-BFGS-B', options={'maxiter':80})
    print("\nOptimisation finished")
    print("Best parameters:")
    labels=["alpha","n2","r1","r2","C0","gamma"]
    for name,val in zip(labels,result.x):
        print(f"  {name} = {val:.3f}")
    print(f"Global χ²/N = {result.fun:.2f}")

if __name__=='__main__':
    main() 