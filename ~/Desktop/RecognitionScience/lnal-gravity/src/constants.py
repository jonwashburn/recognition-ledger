#!/usr/bin/env python3
"""
Physical and Mathematical Constants for LNAL Gravity Theory
"""

import numpy as np

# Mathematical constants
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio ≈ 1.618034

# Physical constants (SI units)
G = 6.67430e-11  # Gravitational constant (m³/kg/s²)
C = 2.99792458e8  # Speed of light (m/s)
H0 = 2.195e-18  # Hubble constant (1/s) ~ 67.4 km/s/Mpc
HBAR = 1.054571817e-34  # Reduced Planck constant (J·s)
K_B = 1.380649e-23  # Boltzmann constant (J/K)

# Astronomical units
M_SUN = 1.98847e30  # Solar mass (kg)
PC = 3.0856775814913673e16  # Parsec (m)
KPC = 3.0856775814913673e19  # Kiloparsec (m)
MPC = 3.0856775814913673e22  # Megaparsec (m)

# LNAL derived constants
A0 = 1.85e-10  # LNAL acceleration scale (m/s²)
L1 = 0.97 * KPC  # First recognition length (m)
L2 = 24.3 * KPC  # Second recognition length (m)
L_PLANCK = np.sqrt(HBAR * G / C**3)  # Planck length (m)

# Recognition Science scales
LAMBDA_EFF = 3.67e-6  # Effective wavelength (m) ~ 3.67 μm
BETA_0 = -(PHI - 1) / PHI**5  # Base flow parameter ≈ -0.055728
MU_0 = PHI**(-3/2)  # Base coupling ≈ 0.497
LAMBDA_C0 = PHI**2  # Base coupling scale ≈ 2.618

# Cosmic parameters
COSMIC_LEDGER_FACTOR = 1.01  # 1% cosmic overhead
RHO_CRIT = 3 * H0**2 / (8 * np.pi * G)  # Critical density (kg/m³)
OMEGA_M = 0.3  # Matter density parameter
OMEGA_LAMBDA = 0.7  # Dark energy density parameter

# Prime sieve factor
PRIME_SIEVE = PHI**(-0.5) * 8 / np.pi**2  # For odd square-free numbers

# Information theory scales
M0 = PHI**(-8) * M_SUN  # Base mass scale (kg)
DELTA_INFO = PHI**(1/8) - 1  # Information debt increment 