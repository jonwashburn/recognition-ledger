# Foundation Strengthening Roadmap

> **Goal:** Eliminate every remaining `sorry` and make the Recognition-Science foundation a *fully-proved*, axiom-free, audited Lean library.

Last audit (`scripts/audit_foundation.py` run 2025-06-28) shows:

* **Axioms:** 0   ✅
* **Sorrys:** 23  ❌  
* **Circular imports:** 0 ✅

The 23 sorrys occur in exactly **7 files**.  We hard-rank them by logical depth and dependency so we can tighten the stack from the bottom (kernel) upward.

---
## 1  Logical-Chain Layer  (`foundation/Core/LogicalChainFix.lean`)
The only missing proofs between the Meta-Principle and Foundation 1 (Discrete-Recognition).

| Line | Lemma | Why it matters |
|------|-------|----------------|
| 58 | `continuous_time_infinite_info` | Shows continuous time needs unbounded information. |
| 72 | `finite_info_capacity` | Binds physical systems to finite Shannon info. |
| 87 | `continuous_time_impossible` | Combines the two lemmas above. |
| 102| `time_dichotomy` | Classical either-or ⇒ gives a discrete "tick". |

**Plan**
1. **Cantor Argument** – Prove `continuous_time_infinite_info` by mapping any `n`-bit encoding to disjoint intervals; use dense ordering to derive ≥ 2ⁿ distinguishable moments ⇒ information grows without bound.
2. **Finite Capacity** – Define `info_content` as `log₂ (card state)` for finite types; leverage existing `Finite` infrastructure + pigeonhole.
3. **Impossible** – Combine (1) and (2): finite bound ∧ unbounded requirement ⇒ contradiction.
4. **Dichotomy** – Use excluded-middle on density; if ¬dense construct `tick t := least s > t` (well-founded by classical choice) and prove the required inequalities.

*Impact*: removes 4 sorrys and gives an *unbroken, proved* chain
``MetaPrinciple ⇒ discrete time ⇒ Foundation₁``.

---
## 2  Derivation Layer (physical constants)
After Step 1 only 19 sorrys remain, all in these physics/constant files:

| File | Sorrys | Dependencies |
|------|--------|--------------|
| `Lensing/ThinLens.lean` | **3** | Pure geometry (independent) |
| `Core/Derivations/CoherenceQuantumDerivation.lean` | **4** | Golden-ratio derivation complete; uses algebra only |
| `Core/Derivations/CoherenceQuantumFixed.lean` | **3** | Needs *atomic_recognition* theorem we already stubbed |
| `Core/Derivations/CosmicBandwidthDerivation.lean` | **4** | Uses `finite_info_capacity` (from Step 1) |
| `Core/Derivations/CostFunctionalDerivation.lean` | **6** | Consumes every constant defined earlier |
| `Core/Derivations/YangMillsMassGap.lean` | **3** | Final consumer |

### Recommended order
1. **ThinLens** – close the 3 optics lemmas (simple `Real` inequalities).
2. **CoherenceQuantum* (7 total)** – now free of circular α/E₍coh₎ dependency.  
   *Prove* `atomic_recognition` via energy spacing in finite Hilbert module.
3. **CosmicBandwidthDerivation** – once `finite_info_capacity` is in place.
4. **CostFunctionalDerivation** – ledger curvature → action principle.
5. **YangMillsMassGap** – last consumer; all constants now available.

*Impact*: brings sorry count to **0**.

---
## 3  CI Guard (Phase 4 of original six-phase plan)
* Add `audit_foundation.py` into GitHub Actions (`.github/workflows/ci.yml`).
* Fail build if:
  * `Axioms > 0`  
  * `Sorrys > 0`  
  * new circular imports detected.

---
## 4  Documentation & Release (Phases 5-6)
* Tag **v1.0-kernel-complete** once CI is green.
* Draft short arXiv paper "Zero-Axiom Kernel for Recognition Science".
* Publish release notes & invite external proofs-as-PRs.

---
### Branch / Work Flow
| Purpose | Branch | Status |
|----------|--------|--------|
| Kernel → definition (no axioms) | `meta-principle-definition` | _merged / PR #‹pending›_ |
| Logical chain proofs | `logical-chain-proof` | _next to create_ |
| Physics constant proofs | `constant-derivations` | _future_ |
| CI integration | `ci-guard` | _future_ |

Each branch must:
1. Pass `lake build`.
2. Pass `python scripts/audit_foundation.py` (0 axioms, ≤ current sorry count).
3. Squash-merge via PR to `main`.

---
## Immediate Action Item
Create branch **`logical-chain-proof`** and replace the four TODO blocks in `Core/LogicalChainFix.lean` as per the plan above.  This delivers the first full, axiom-free theorem chain from the Meta-Principle to discrete time. 