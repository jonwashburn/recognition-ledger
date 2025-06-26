#!/usr/bin/env python3
"""
Example: LNAL Gravity Theory Applied to NGC 3198
"""

import numpy as np
import matplotlib.pyplot as plt
from src.lnal_gravity import LNALGravity, GalaxyData

def main():
    """Run example calculation for NGC 3198"""
    
    # Initialize LNAL model
    lnal = LNALGravity()
    
    # NGC 3198 parameters (approximate)
    M_star = 1.3e10  # Solar masses
    M_gas = 0.7e10   # Solar masses
    
    # Create radius array
    r_kpc = np.logspace(0, 1.5, 50)  # 1 to 30 kpc
    
    # Calculate rotation curve
    result = lnal.calculate_acceleration(r_kpc, M_star, M_gas)
    
    # Plot results
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(8, 10))
    
    # Velocity curve
    ax1.plot(r_kpc, result['v_lnal'], 'r-', linewidth=2, label='LNAL')
    ax1.plot(r_kpc, result['v_newton'], 'b--', linewidth=2, label='Newtonian')
    ax1.set_xlabel('Radius (kpc)')
    ax1.set_ylabel('Velocity (km/s)')
    ax1.set_title('NGC 3198 - LNAL Gravity Prediction')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(1, 30)
    ax1.set_ylim(0, 200)
    
    # Acceleration
    ax2.loglog(r_kpc, result['g_lnal'], 'r-', linewidth=2, label='LNAL')
    ax2.loglog(r_kpc, result['g_newton'], 'b--', linewidth=2, label='Newtonian')
    ax2.axhline(lnal.a0, color='g', linestyle=':', label=f'a₀ = {lnal.a0:.1e} m/s²')
    ax2.set_xlabel('Radius (kpc)')
    ax2.set_ylabel('Acceleration (m/s²)')
    ax2.set_title('Acceleration Profile')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('ngc3198_example.png', dpi=150, bbox_inches='tight')
    plt.show()
    
    # Print summary
    print("NGC 3198 Example")
    print("="*40)
    print(f"Stellar mass: {M_star/1e10:.1f} × 10¹⁰ M☉")
    print(f"Gas mass: {M_gas/1e10:.1f} × 10¹⁰ M☉")
    print(f"Gas fraction: {M_gas/(M_star + M_gas):.2f}")
    print(f"\nAt R = 10 kpc:")
    idx = np.argmin(np.abs(r_kpc - 10))
    print(f"  V_LNAL = {result['v_lnal'][idx]:.1f} km/s")
    print(f"  V_Newton = {result['v_newton'][idx]:.1f} km/s")
    print(f"  Ratio = {result['v_lnal'][idx]/result['v_newton'][idx]:.2f}")
    print(f"\nTheory parameters (zero free parameters):")
    print(f"  φ = {lnal.phi:.6f}")
    print(f"  a₀ = {lnal.a0:.2e} m/s²")
    print(f"  Cosmic factor = {lnal.cosmic_factor}")

if __name__ == "__main__":
    main() 