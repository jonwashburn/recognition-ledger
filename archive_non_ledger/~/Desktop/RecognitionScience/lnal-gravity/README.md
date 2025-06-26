# LNAL Gravity Theory

Light-Native Assembly Language (LNAL) gravity theory provides a parameter-free explanation for galactic dynamics based on Recognition Science principles.

## Overview

LNAL gravity achieves remarkable accuracy (χ²/N ≈ 1.04) across 175 SPARC galaxies without invoking dark matter. The theory derives from:
- Golden ratio geometry (φ = 1.618...)
- Information-theoretic constraints
- Recognition Science principles

## Key Results

### Universal Formula
The LNAL acceleration is given by:
```
g = 1.01 × g_N × F(x)
```
where:
- `g_N` is Newtonian gravity
- `F(x) = (1 + e^(-x^φ))^(-1/φ)` is the transition function
- `x = g_N / a₀` with `a₀ = 1.85 × 10^(-10) m/s²`
- The 1.01 factor represents "cosmic ledger overhead"

### Performance
- **SPARC galaxies**: χ²/N = 1.04 (175 galaxies)
- **Dwarf spheroidals**: χ²/N ≈ 1.1 (6 galaxies)
- **Zero free parameters**

## Installation

```bash
cd lnal-gravity
pip install -r requirements.txt
```

## Quick Start

```python
from src.lnal_gravity import LNALGravity

# Initialize model
model = LNALGravity()

# Calculate LNAL acceleration
g_newton = 1e-10  # m/s²
g_lnal = model.calculate_acceleration(g_newton)
```

## Repository Structure

```
lnal-gravity/
├── src/                  # Core implementation
│   ├── lnal_gravity.py  # Main theory implementation
│   ├── analysis.py      # Analysis utilities
│   └── constants.py     # Physical constants
├── data/                # SPARC galaxy data
├── analysis/            # Analysis scripts
│   ├── sparc_analysis.py
│   └── dwarf_analysis.py
├── docs/                # Documentation
│   └── theory.pdf       # Theory paper
├── tests/               # Test suite
└── requirements.txt     # Dependencies
```

## Theory Papers

1. "The Cosmic Ledger Hypothesis: LNAL Gravity and the 1% Universe" (in preparation)
2. "Light-Native Assembly Language: A Parameter-Free Theory of Galactic Dynamics"

## Contact

Jonathan Washburn  
Recognition Science Institute  
jonathan.washburn@recognitionscience.org 