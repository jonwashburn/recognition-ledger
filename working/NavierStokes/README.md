# NavierStokes Working Directory

[![NavierStokes CI](https://github.com/jonwashburn/recognition-ledger/actions/workflows/navier-stokes-ci.yml/badge.svg)](https://github.com/jonwashburn/recognition-ledger/actions/workflows/navier-stokes-ci.yml)

This is the active development directory for the Navier-Stokes global regularity proof under the Recognition Science framework.

## Status
- **Development Stage**: Active development
- **Lean Version**: 4.7.0
- **Main Theorem**: `NavierStokesLedger.Theorems.navier_stokes_global_regularity`

## Structure
```
NavierStokes/
├── lakefile.lean           # Lean build configuration
├── lean-toolchain          # Lean version specification
└── Src/
    └── NavierStokesLedger/
        ├── Theorems.lean           # Main theorem statements (PUBLIC)
        ├── Constants.lean          # All constants in one place (PUBLIC)
        ├── Basic.lean              # Basic definitions and spaces
        ├── BasicDefinitions.lean   # Core lemmas
        ├── VorticityBound.lean     # Main vorticity bound proof
        ├── UnconditionalProof.lean # Combines all pieces
        ├── LedgerAxioms.lean       # RS axiom interface
        ├── Bootstrap/              # Bootstrap lemmas
        ├── FluidDynamics/          # Fluid-specific definitions
        └── Harnack/                # Harnack inequality tools
```

## Key Results

The main theorem states:
```lean
theorem navier_stokes_global_regularity
  {u₀ : ℝ³ → ℝ³} 
  (h_div : divergence_free u₀) 
  (h_smooth : u₀ ∈ H⁴ ∩ L²) 
  (h_energy : ∫ |u₀|² < ∞) :
  ∀ t > 0, ∃! u : ℝ³ → ℝ³, 
    is_solution_nse u u₀ ∧ 
    u ∈ C^∞(ℝ³) ∧
    ∫ |u(t)|² ≤ ∫ |u₀|²
```

## Key Constants Required
The proof depends on establishing:
- `C* = 2 * C₀ * √(4π) < φ⁻¹`
- Where `C₀` is the geometric depletion rate from the RS framework

All constants are now centralized in `Constants.lean`.

## Build Instructions
```bash
lake build
```

## CI Status
The project has continuous integration that:
- Builds all Lean files
- Checks for remaining `sorry` placeholders
- Reports the count of incomplete proofs

## Next Steps
1. Complete the derivation of C₀ from RS axioms
2. Prove the C* < φ⁻¹ bound
3. Fill remaining `sorry` placeholders
4. Move to `physics/` when complete (0 sorries) 