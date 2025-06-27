# Gravity Layer Dependency Audit (Phase 0 – step 0.2)

Generated 2025-06-27

---
## 1. Local namespace `Constants` duplicates
| File | Constants defined | Already defined in foundation? |
|------|-------------------|---------------------------------|
| `Util/PhysicalUnits.lean` | `c`, `G`, `ℏ`, etc. (proper SI wrapper) | foundation/Util/Units.lean provides equivalent — **merge** |
| `Quantum/CollapseCriterion.lean` | `ℏ` only (duplicate) | duplicate → remove after Phase 1 |
| `Lensing/Convergence.lean` | `G` only (duplicate) | duplicate → remove after Phase 1 |

## 2. Local axioms in gravity/
| Axiom | File | Planned replacement |
|-------|------|--------------------|
| `unitary_preserves_superposition` | Quantum/CollapseCriterion | Phase 2 row 1 |
| `quantum_evolution_continuous` | ″ | Phase 2 row 2 |
| `quantum_nonclassical_open` | ″ | Phase 2 row 3 |
| `thin_lens_approximation` | Lensing/Convergence | Phase 2 row 4 |
| `bandwidth_conservation` | Quantum/BandwidthCost | **NEW** candidate: prove via ∑ allocations ≤ B_total in `foundation/Physics/Bandwidth` |
| `bandwidth_sum` | Cosmology/BandwidthLambda | same proof as above re-used |

## 3. Import graph (excerpt)
```
Quantum/CollapseCriterion → Quantum/BandwidthCost → Util/PhysicalUnits → foundation.Util.Units
Lensing/Convergence      → Util/PhysicalUnits      → foundation.Util.Units
Cosmology/BandwidthLambda→ Quantum/BandwidthCost
```
At present gravity layer *does not* import anything from `foundation.Core` or `foundation.Derivations`.  That will change once RecognitionWeight is moved.

## 4. Action items for Phase 1
1. Delete `namespace Constants` blocks in gravity/* once shared constants are imported.
2. Add `import Foundation.Physics.Bandwidth` at top of gravity files (after module is created).
3. Replace `Constants.G`, `Constants.ℏ`, etc. with `Foundation.Constants.G` (or the chosen alias).

---
Commit prepared: audit document added. 