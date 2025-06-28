# Gravity Analysis Scripts

This directory contains Python scripts for analyzing galaxy rotation curves and cosmological data using the Recognition Science bandwidth triage model.

## Data Location

All scripts expect SPARC galaxy rotation data to be in:
```
../data/Rotmod_LTG/
```

## Script Categories

### Core Analysis Scripts
- `lnal_bandwidth_triage_model.py` - Main bandwidth triage implementation
- `lnal_complete_gravity_solver.py` - Complete gravity solver
- `lnal_exact_solver.py` - Exact solution methods

### Model Variants
- `lnal_forward_model_v2.py` - Forward modeling approach
- `lnal_3d_model.py` - 3D galaxy modeling
- `lnal_ml_emulator.py` - Machine learning emulator

### Analysis Tools
- `lnal_sparc_loader.py` - SPARC data loader utilities
- `lnal_component_analyzer.py` - Component analysis
- `lnal_hierarchical_bayes.py` - Bayesian analysis

### Cosmology
- `lnal_cosmology_v2.py` - Cosmological calculations
- `lnal_dark_energy_v2.py` - Dark energy analysis
- `lnal_CMB_fit.py` - CMB fitting

### Utilities
- `lnal_final_pipeline.py` - Full analysis pipeline
- `lnal_sparc_deep_dive.py` - Detailed SPARC analysis
- `lnal_tuned_galaxy_fitter.py` - Galaxy-specific tuning

## Cleanup Notes

Removed numbered duplicates (e.g., `script 2.py`, `script 3.py`) to maintain a single version of each script. 