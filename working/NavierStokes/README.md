# NavierStokes Working Directory

This is the active development directory for the Navier-Stokes global regularity proof under the Recognition Science framework.

## Status
- **Development Stage**: Active development
- **Lean Version**: 4.7.0
- **Main Proof File**: `Src/NavierStokesLedger/VorticityBound.lean`

## Structure
```
NavierStokes/
├── lakefile.lean           # Lean build configuration
├── lean-toolchain          # Lean version specification
└── Src/
    └── NavierStokesLedger/
        ├── Basic.lean              # Basic definitions and spaces
        ├── BasicDefinitions.lean   # Constants and core lemmas
        ├── VorticityBound.lean     # Main proof (71KB)
        ├── LedgerAxioms.lean       # RS axiom interface
        ├── Bootstrap/              # Bootstrap lemmas
        ├── FluidDynamics/          # Fluid-specific definitions
        └── Harnack/                # Harnack inequality tools
```

## Key Constants Required
The proof depends on establishing:
- `C* = 2 * C₀ * √(4π) < φ⁻¹`
- Where `C₀` is the geometric depletion rate from the RS framework

## Build Instructions
```bash
lake build
```

## Next Steps
1. Complete the derivation of C₀ from RS axioms
2. Prove the C* < φ⁻¹ bound
3. Fill remaining `sorry` placeholders
4. Move to `physics/` when complete 