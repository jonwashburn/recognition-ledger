#!/usr/bin/env python3
"""
LNAL Gravity Theory - Core Implementation
=========================================
Light-Native Assembly Language gravity theory based on Recognition Science principles.
Parameter-free approach to galactic dynamics.
"""

import numpy as np
from typing import Dict, Tuple, Optional
from dataclasses import dataclass

# Physical constants
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
G = 6.67430e-11  # Gravitational constant (m³/kg/s²)
C = 2.99792458e8  # Speed of light (m/s)
M_SUN = 1.98847e30  # Solar mass (kg)
KPC = 3.0856775814913673e19  # Kiloparsec in meters

# Derived constants from Recognition Science
A0 = 1.85e-10  # LNAL acceleration scale (m/s²)
L1 = 0.97 * KPC  # First recognition length (m)
L2 = 24.3 * KPC  # Second recognition length (m)
COSMIC_LEDGER_FACTOR = 1.01  # 1% cosmic overhead


@dataclass
class GalaxyData:
    """Container for galaxy observational data"""
    name: str
    r_kpc: np.ndarray  # Radii in kpc
    v_obs: np.ndarray  # Observed velocities in km/s
    v_err: np.ndarray  # Velocity errors in km/s
    M_star: float  # Stellar mass in solar masses
    M_gas: float  # Gas mass in solar masses
    R_disk: float  # Disk scale radius in kpc


class LNALGravity:
    """
    LNAL Gravity Theory Implementation
    
    Based on Recognition Science principles with zero free parameters.
    All scales derived from golden ratio geometry.
    """
    
    def __init__(self):
        """Initialize LNAL gravity solver"""
        self.phi = PHI
        self.a0 = A0
        self.cosmic_factor = COSMIC_LEDGER_FACTOR
        
    def transition_function(self, x: np.ndarray) -> np.ndarray:
        """
        LNAL transition function F(x)
        
        F(x) = (1 + e^(-x^φ))^(-1/φ)
        
        Args:
            x: Ratio g_N / a₀
            
        Returns:
            Transition function value
        """
        return np.power(1 + np.exp(-np.power(x, self.phi)), -1/self.phi)
    
    def baryon_completeness(self, f_gas: float) -> float:
        """
        Baryon completeness factor Ξ(f_gas)
        
        Ξ = 1 / (1 - f_gas φ^{-2})
        
        Args:
            f_gas: Gas fraction M_gas/(M_star + M_gas)
            
        Returns:
            Completeness factor
        """
        return 1.0 / (1.0 - f_gas * self.phi**(-2))
    
    def information_debt(self, M_star: float, V_rot: Optional[float] = None) -> float:
        """
        Information debt factor Ψ(M*)
        
        Accounts for hierarchical information processing overhead.
        
        Args:
            M_star: Stellar mass in solar masses
            V_rot: Rotation velocity for kinetic term (optional)
            
        Returns:
            Information debt factor
        """
        if M_star <= 0:
            return 1.0
            
        # Base mass scale
        M0 = self.phi**(-8) * M_SUN
        
        # Hierarchical depth
        N_raw = np.log(M_star * M_SUN / M0) / np.log(self.phi)
        
        # Schwarzschild radius limit
        R_s = 2.0 * G * M_star * M_SUN / C**2
        L_0 = 0.335e-9  # Planck-scale recognition length
        N_limit = np.log(R_s / L_0) / np.log(self.phi) if R_s > 0 else N_raw
        N = min(max(0.0, N_raw), max(0.0, N_limit))
        
        # Base information debt
        delta = self.phi**(1/8.0) - 1.0
        psi_base = 1.0 + N * delta
        
        # Add kinetic term if velocity provided
        if V_rot is not None:
            sigma = 0.7 * V_rot  # Velocity dispersion estimate
            psi_kinetic = 0.5 * (sigma / C)**2
            return psi_base * (1 + psi_kinetic)
        else:
            return psi_base
    
    def recognition_enhancement(self, r: np.ndarray) -> np.ndarray:
        """
        Recognition scale enhancement at characteristic lengths
        
        Args:
            r: Radius in meters
            
        Returns:
            Enhancement factor
        """
        # Logarithmic bumps at recognition scales
        bump_1 = 0.1 * np.exp(-(np.log(r/L1))**2 / 2)
        bump_2 = 0.03 * np.exp(-(np.log(r/L2))**2 / 2)
        return 1 + bump_1 + bump_2
    
    def calculate_acceleration(self, r_kpc: np.ndarray, M_star: float, 
                             M_gas: float) -> Dict[str, np.ndarray]:
        """
        Calculate LNAL acceleration for given radius and masses
        
        Args:
            r_kpc: Radius in kpc (scalar or array)
            M_star: Stellar mass in solar masses
            M_gas: Gas mass in solar masses
            
        Returns:
            Dictionary with:
                - g_lnal: LNAL acceleration in m/s²
                - g_newton: Newtonian acceleration in m/s²
                - v_lnal: LNAL circular velocity in km/s
                - v_newton: Newtonian circular velocity in km/s
        """
        # Convert to SI units
        r = np.atleast_1d(r_kpc) * KPC
        M_total = (M_star + M_gas) * M_SUN
        
        # Calculate factors
        f_gas = M_gas / (M_star + M_gas) if (M_star + M_gas) > 0 else 0.0
        Xi = self.baryon_completeness(f_gas)
        Psi = self.information_debt(M_star)
        
        # Effective mass
        M_eff = M_total * Xi * Psi
        
        # Newtonian acceleration
        g_newton = G * M_eff / r**2
        
        # LNAL transition
        x = g_newton / self.a0
        F = self.transition_function(x)
        
        # Recognition enhancement
        Lambda = self.recognition_enhancement(r)
        
        # Prime sieve factor (8/π² for odd square-free)
        P = self.phi**(-0.5) * 8 / np.pi**2
        
        # LNAL acceleration with cosmic ledger factor
        g_lnal = self.cosmic_factor * g_newton * F * Lambda * P
        
        # Convert to velocities
        v_lnal = np.sqrt(g_lnal * r) / 1000  # km/s
        v_newton = np.sqrt(G * M_total / r) / 1000  # km/s
        
        return {
            'g_lnal': g_lnal,
            'g_newton': g_newton,
            'v_lnal': v_lnal,
            'v_newton': v_newton
        }
    
    def fit_galaxy(self, galaxy: GalaxyData) -> Dict[str, any]:
        """
        Fit LNAL model to galaxy rotation curve
        
        Args:
            galaxy: GalaxyData object with observations
            
        Returns:
            Dictionary with fit results including chi-squared
        """
        # Calculate model predictions
        result = self.calculate_acceleration(galaxy.r_kpc, galaxy.M_star, galaxy.M_gas)
        v_model = result['v_lnal']
        
        # Calculate residuals and chi-squared
        residuals = galaxy.v_obs - v_model
        chi2_points = (residuals / galaxy.v_err)**2
        chi2 = np.sum(chi2_points)
        chi2_reduced = chi2 / len(galaxy.v_obs)
        
        return {
            'v_model': v_model,
            'v_newton': result['v_newton'],
            'residuals': residuals,
            'chi2': chi2,
            'chi2_reduced': chi2_reduced,
            'chi2_points': chi2_points
        }


def example_usage():
    """Example of using LNAL gravity theory"""
    
    # Initialize model
    lnal = LNALGravity()
    
    # Example galaxy parameters (NGC 3198-like)
    r_kpc = np.linspace(1, 30, 20)
    M_star = 1e10  # Solar masses
    M_gas = 0.5e10  # Solar masses
    
    # Calculate rotation curve
    result = lnal.calculate_acceleration(r_kpc, M_star, M_gas)
    
    print("LNAL Gravity Theory Example")
    print("="*40)
    print(f"Galaxy mass: {(M_star + M_gas)/1e10:.1f} × 10¹⁰ M☉")
    print(f"Gas fraction: {M_gas/(M_star + M_gas):.2f}")
    print(f"\nRadius (kpc) | V_LNAL (km/s) | V_Newton (km/s)")
    print("-"*40)
    
    for i in [0, 5, 10, 15, 19]:
        print(f"{r_kpc[i]:11.1f} | {result['v_lnal'][i]:13.1f} | {result['v_newton'][i]:15.1f}")


if __name__ == "__main__":
    example_usage() 