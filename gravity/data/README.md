# Gravity Data Directory

This directory contains the SPARC galaxy rotation curve data and analysis results.

## Directory Structure

### Input Data
- `Rotmod_LTG/` - SPARC galaxy rotation curve data files (175 galaxies)
  - Format: `GALAXY_NAME_rotmod.dat`
  - Contains radius, velocity, and uncertainty measurements

### Analysis Results
- `lnal_3d_results/` - 3D model outputs
- `lnal_component_results/` - Component analysis results
- `lnal_forward_v2_results/` - Forward model v2 results
- `lnal_ml_emulator_results/` - Machine learning emulator outputs
- `lnal_pure_results/` - Pure LNAL model results
- `lnal_results/` - General LNAL analysis results
- `lnal_tuned_galaxies/` - Galaxy-specific tuned parameters

## Data Format

### Rotmod Files
Each `.dat` file contains columns:
1. Radius (kpc)
2. Observed velocity (km/s)
3. Velocity uncertainty (km/s)
4. Additional model parameters (varies by galaxy)

### Result Files
Results are typically stored as:
- `.json` - Summary statistics and parameters
- `.csv` - Detailed numerical results
- `.png` - Plots (excluded from git) 