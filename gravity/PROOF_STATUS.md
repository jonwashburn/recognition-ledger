# Gravity Module Proof Status

Last Updated: 2024-12-26

## Overview

This document tracks the proof status of all theorems in the gravity module. We maintain a strict **no-axiom, no-sorry** policy in production code.

## Status Categories

- ✅ **Proven**: Complete proof with no sorries
- 🟡 **Commented**: Theorem statement exists but proof deferred (in comments)
- 🔴 **Sorry**: Contains sorry (must be resolved or commented out)
- 📐 **Numeric**: Requires numerical computation tools
- ⚠️ **Axiom**: Stated as axiom (should be theorem eventually)

## Summary
- **Total Theorems**: 45
- **Proven**: 30 (66.7%)
- **Remaining Sorries**: 15 (33.3%)
- **Files with Sorries**: 8/17

## Completed Files (Sorry-Free)
✅ Core/RecognitionWeight.lean  
✅ Core/TriagePrinciple.lean  
✅ Util/PhysicalUnits.lean  
✅ All JSON prediction files  
✅ All Python scripts  

## Files with Remaining Sorries

### 1. Cosmology/BandwidthLambda.lean (3 sorries)
- `expansion_history` for z ∈ (0.5, 1], (1, 2], (2, 3] - needs detailed numerical bounds
- Status: Technical numerical verification

### 2. Quantum/CollapseCriterion.lean (4 sorries)
- `evolutionOperator_unitary` - needs matrix exponential unitarity lemma
- `collapse_time_exists` (3 physics assumptions):
  - Physical states evolve continuously
  - Unitary evolution preserves superposition
  - Continuous positive functions bounded below on intervals

### 3. Quantum/BandwidthCost.lean (3 sorries)
- `optimalAllocation_feasible` - needs maxNorm ≤ 1 assumption
- `bandwidth_criticality` - needs Jensen's inequality application
- One helper sorry in allocation bound

### 4. Quantum/BornRule.lean (1 sorry)
- `max_entropy_uniform` - needs limit x log x → 0 as x → 0⁺

### 5. Lensing/Convergence.lean (3 sorries)
- `convergence_radial_eq` - chain rule calculation
- `convergence_enhancement` - algebraic simplification after factoring
- `shear_modified` - similar to convergence calculation

### 6. Core/BandwidthConstraints.lean (commented theorems)
- Several theorems commented out pending implementation

### 7. Derivations/AccelerationScale.lean (commented theorems)
- Detailed derivations commented out

### 8. Util/Variational.lean (1 sorry in FirstVariation)
- `is_derivative` definition uses undefined δF

## Categories of Remaining Work

### 1. Numerical Verification (3 sorries)
- Interval arithmetic for cosmological expansion history
- Can be resolved with finer interval subdivision

### 2. Mathematical Library Gaps (5 sorries)
- Matrix exponential unitarity
- Jensen's inequality for convex functions
- Limit of x log x at zero
- Chain rule for polar coordinates

### 3. Physics Assumptions (3 sorries)
- Continuous evolution of quantum states
- Unitary evolution preserves superposition
- Positive continuous functions bounded below

### 4. Technical Calculations (4 sorries)
- Algebraic simplifications in lensing
- Bandwidth allocation bounds
- Polar/Cartesian transformations

## Progress Since Last Update
- ✅ Completed `dimension_injective` proof
- ✅ Upgraded `entropy_convex` to `StrictConvexOn`
- ✅ Implemented `SchrodingerEvolution` structure
- ✅ Added `continuous_amplitude` helper
- ✅ Implemented equal division allocation
- ✅ Added `laplacian_radial` lemma
- ✅ Moved unused variational theorems to future work

## Next Steps
1. Import or backport matrix exponential unitarity from mathlib
2. Complete numerical bounds for expansion history
3. Add Jensen's inequality application for criticality
4. Finish polar coordinate transformations for lensing

## Guidelines

- Never commit files with uncommented `sorry`
- Use `-- theorem name ... := by sorry` for deferred proofs
- Mark numeric proofs with `TODO(numeric)`
- Update this file with every PR 