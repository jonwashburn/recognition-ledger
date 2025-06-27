# Foundation API (first draft)

> **Scope** This document lists publicly available Lean modules, constants and theorems in `foundation/`.  It is a *machine-generated* first pass created on 2025-06-27; entries will be expanded and verified as integration proceeds.

---
## Directory map

| Path | Brief description |
|------|-------------------|
| `foundation/Core/` | proofs of the eight recognition axioms directly from the meta-principle |
| `foundation/Derivations/` | golden-ratio cascade & all fundamental constants (φ, E_coh, τ₀, λ_P, …) |
| `foundation/Geometry/` | voxel lattice, causal diamonds, scale operator Σ |
| `foundation/Physics/` | high-level theorems (to-be-added RecognitionWeight) |
| `foundation/Quantum/` | basic unitary evolution lemmas, Born rule derivation |
| `foundation/Util/` | dimension-safe units system, common tactics |

---
## Key constants

| Constant | Type | Defined in |
|----------|------|-----------|
| `φ` | `ℝ` | `Derivations.GoldenRatio` |
| `E_coh` | `Quantity ⟨1,0,0⟩` | `Derivations.CoherenceQuantum` |
| `τ₀` | `ℝ` | `Derivations.TickInterval` |
| `ℓ_Planck` | `ℝ` | `Geometry.Voxel` |

---
## Representative theorems

| Theorem | Statement (human) | Location |
|---------|-------------------|----------|
| `meta_principle_implies_A1` | "Nothing cannot recognize itself" ⇒ Discrete updates (Axiom A1) | `Core.DiscreteRecognition` |
| `eight_beat_closure` | Tick⁸ commutes with all symmetries | `Core.EightBeat` |
| `golden_ratio_unique` | ½(x+1/x) minimal ⇔ x = φ | `Derivations.GoldenRatio` |
| `energy_cascade` | `E_r = E_coh * φ^r` | `Derivations.EnergyCascade` |

**TODO**: auto-extract signatures with `lake print-path` + `lean --server`.

---
## Next actions
1. Complete inventory of constants and theorems ("T-list").
2. Export it as JSON for programmatic check during CI (Phase 4). 