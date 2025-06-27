# Road-map: Integrating "gravity/" with the Foundation Layer

*Objective*: derive the entire bandwidth-limited gravity module directly from the single meta-principle proved in `foundation/`, eliminating the few remaining physical axioms and ensuring every Lean dependency flows **Meta-Principle → Eight Axioms → Recognition Weight → Gravity**.

---
## Phase 0  Reconnaissance (1 day)
| Step | Action |
|------|--------|
|0.1|Catalogue public theorems in `foundation/` → create `docs/foundation_API.md` summarising names & types|
|0.2|Inventory imports in `gravity/` → list constants / axioms duplicated locally|

---
## Phase 1  Namespace Harmonisation (1–2 days)
1. **Move recognition-weight** definition to `foundation/Physics/Bandwidth.lean`, prove it from the eight axioms and cost functional `J(x)=½(x+1/x)`.
2. Update gravity files to `import Foundation.Physics.Bandwidth`.
3. Replace hard-coded constants (`G`, `ℏ`, …) with canonical ones from `foundation/Util/Units.lean`.

---
## Phase 2  Axiom Elimination (4–7 days)
| Local axiom | Plan to replace |
|-------------|-----------------|
|`unitary_preserves_superposition`|Prove in `foundation/Quantum/UnitaryBasics.lean` using preservation of inner product|
|`quantum_evolution_continuous`|Use `Matrix.exponential` continuity (mathlib) → `formal/Quantum/SchrodingerContinuity.lean`|
|`quantum_nonclassical_open`|Topological argument: non-classical set is open complement of closed set|
|`thin_lens_approximation`|Formal lemma: if `|w'| ≤ ε·w/R` & `|w''| ≤ ε·w/R²` then shear term error ≤ ε; parameterise ε≤10⁻³|

All four proofs remove the last ad-hoc axioms from gravity.

---
## Phase 3  Pipeline Documentation (2 days)
1. Add `docs/PIPELINE.md` linking each Lean theorem to its downstream dependants.
2. Cross-link LaTeX manuscripts with Lean theorem names (`\href{…}{Theorem BW.3}`).

---
## Phase 4  CI & Badging (½ day)
* Extend `.github/workflows/lean.yml` to fail on any `sorry` or `axiom` outside `formal/Axioms.lean`.
* Add README badge "Lean proofs ✔".

---
## Phase 5  House-keeping (optional)
* Move any unavoidable domain axioms to `formal/Axioms.lean` with full documentation.
* De-duplicate constant definitions into `foundation/Constants.lean`.

---
### Deliverables & Timeline
*Phase 0–1*: 2–3 days • *Phase 2*: 1 week • *Phase 3–4*: 2 days  
**Total ≈ 12 days** concentrated work → full derivation of gravity from the meta-principle with *zero* extra axioms. 