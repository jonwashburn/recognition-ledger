# Gravity Module Proof Status

Last Updated: 2024-12-26

## Overview

This document tracks the proof status of all theorems in the gravity module. We maintain a strict **no-axiom, no-sorry** policy in production code.

## Status Categories

- ✅ **Proven**: Complete proof with no sorries
- 🟡 **Commented**: Theorem statement exists but proof deferred (in comments)
- 🔴 **Sorry**: Contains sorry (must be resolved or commented out)
- 📐 **Numeric**: Requires numerical computation tools

## File Status

### Core Module (✅ Complete - No Sorries)

#### gravity/Core/TriagePrinciple.lean
- ✅ `triage_principle` - Urgent systems get frequent updates
- ✅ `solar_systems_newtonian` - Solar systems maintain Newtonian gravity
- ✅ `galaxies_have_lag` - Galaxies experience refresh lag  
- ✅ `dark_matter_emergence` - Dark matter emerges in galaxies
- ✅ `dark_energy_emergence` - Dark energy at cosmic scales
- ✅ `triage_saves_bandwidth` - Bandwidth reduction calculation
- ✅ `dwarf_galaxy_enhancement` - Dwarf galaxies have same triage factor

#### gravity/Core/BandwidthConstraints.lean
- 🟡 `galaxy_information_content` - Requires numerical bounds (commented)
- 🟡 `channel_capacity` - List summation machinery (commented)
- 🟡 `optimal_refresh_interval` - Lagrangian optimization (commented)
- 🟡 `information_delay_scaling` - Requires optimal_refresh_interval (commented)

#### gravity/Core/RecognitionWeight.lean
- 🟡 `recognition_weight_nonneg` - Needs positivity of n(r), ζ(r) (commented)
- 🟡 `recognition_weight_mono_in_T` - Needs monotonicity helpers (commented)

### Derivations Module (✅ Complete - No Sorries)

#### gravity/Derivations/AccelerationScale.lean
- ✅ `a0_not_free_parameter` - Direct calculation from galaxy timescale
- ✅ `T_dyn_decreases_with_a` - Monotonicity of dynamical time
- ✅ `high_acceleration_small_Tdyn` - High accelerations → short times
- ✅ `low_acceleration_large_Tdyn` - Low accelerations → long times
- ✅ `deep_MOND_scaling` - Deep MOND regime sqrt(a × a₀)
- ✅ `complexity_affects_weight_simple` - Gas fraction affects complexity
- 🟡 `a0_emergence` - Numerical verification (commented)
- 🟡 `complexity_affects_weight` - Needs Real.rpow injectivity (commented)

### Utility Module (🔴 Contains Sorries)

#### gravity/Util/Variational.lean
- ✅ `entropy_convex` - x log x is convex (proven!)
- 🔴 `euler_lagrange` - Integration by parts needed
- 🔴 `divergence_theorem_gaussian` - Requires Stokes' theorem

#### gravity/Util/PhysicalUnits.lean
- ✅ All definitions complete (no theorems)

### Quantum Module (🔴 Contains Sorries)

#### gravity/Quantum/BandwidthCost.lean
- ✅ `coherent_scaling` - n² scaling proven
- 🔴 `classical_scaling` - log n < n for n > 1
- 🔴 `criticalSize` - Solving n² ≈ log n
- ⚠️ `bandwidth_conservation` - Currently an axiom (should be theorem)

#### gravity/Quantum/BornRule.lean
- 🔴 `born_rule` - Main theorem (optimization proof incomplete)
- 🔴 `born_functional_convex` - Apply entropy_convex
- 🔴 `born_critical_point` - Lagrange multiplier condition
- 🔴 `zero_temperature_limit` - Limit analysis

#### gravity/Quantum/CollapseCriterion.lean
- ✅ `collapse_criterion` - Definition equivalence
- ✅ `collapse_time_decreasing` - 1/n² scaling proven
- 🔴 `eventual_collapse` - Asymptotic n² > log n
- 🔴 `measurement_causes_collapse` - Log monotonicity
- 🔴 `decoherence_scaling` - Unit conversion

### Cosmology Module (🔴 Contains Sorries)

#### gravity/Cosmology/BandwidthLambda.lean
- ✅ `dark_energy_emergence` - Λ_eff bounds proven
- ✅ `structure_correlation` - Anti-correlation proven (modulo Λ₀ > 0)
- 🔴 `high_bandwidth_limit` - ε-δ proof incomplete
- 🔴 `coincidence_solution` - ODE solution needed

### Lensing Module (🔴 Contains Sorries)

#### gravity/Lensing/Convergence.lean
- 🔴 `exponentialDisk` - Positivity constraints
- 🔴 `enhanced_convergence` - Show w > 1
- 🔴 `lensing_dynamics_consistency` - Numerical bounds
- 🔴 `exponential_convergence` - Integration by parts
- 🔴 `signal_peak` - Optimization over R

## Resolution Priority

1. **Immediate** (blocking other work):
   - `entropy_convex` dependencies in BornRule.lean
   - Positivity lemmas for RecognitionWeight.lean

2. **High** (core functionality):
   - `eventual_collapse` - Critical for quantum interpretation
   - `measurement_causes_collapse` - Measurement theory

3. **Medium** (completeness):
   - Variational calculus lemmas
   - Numerical bounds and estimates

4. **Low** (nice to have):
   - Cosmological ODE solutions
   - Lensing integrals

## Next Steps

1. Create `Util/Positivity.lean` with lemmas about positive functions
2. Complete Born rule proof using existing entropy_convex
3. Add numerical evaluation framework for bounds
4. Consider moving complex proofs to separate research files

## Guidelines

- Never commit files with uncommented `sorry`
- Use `-- theorem name ... := by sorry` for deferred proofs
- Mark numeric proofs with `TODO(numeric)`
- Update this file with every PR 