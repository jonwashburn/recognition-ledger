# Foundation‐Proof Hardening Plan

_Target — the entire `foundation/` tree compiles with **zero** `axiom`, `sorry`, circular imports, or placeholder constants.  Result is a "green" foundation on which every other layer can rely._

---

## 0  Baseline Audit  (½ day)

| Task | Output | Success Metric |
|------|--------|----------------|
| 0-A | Script `scripts/audit_foundation.py` that scans `foundation/` for `axiom\|sorry` and circular imports. | Script prints a checklist table *(file, line, issue)* and exits non-zero if any issue found. |
| 0-B | Generated markdown ledger `docs/Foundation_Proof_Ledger.md`. | Every file listed with ✅ / ❌ flags for: axioms, sorrys, circular-import risk. |

---

## 1  Parameter Layer Cleanup  (1 day)

### 1-A   `Parameters/RealConstants.lean`
* Replace `golden_ratio_property` proof
  ```lean
  theorem golden_ratio_property : φ ^ 2 = φ + 1 := by
    simp [φ] ; field_simp ; ring
  ```
* Remove helper lemmas (`φ_pos`, etc.) or formalise them fully.

### 1-B   `Parameters/Constants.lean`
* Delete file **OR** shrink to re-export only:
  ```lean
  import foundation.Parameters.RealConstants
  export RecognitionScience.Constants
  ```
* Ensure no derivation imports remain.

---

## 2  Core Structures Repair  (2 days)

### 2-A   `Core/Finite.lean`
1. Move helper `conservation_satisfied_implies_equal` to `foundation/Helpers/Conservation.lean`.
2. Provide full proofs; remove `sorry`s and unused `omega` import.

### 2-B   `Core/EightFoundations.lean`  **(main blocker)**
1. Extract narrative to `docs/EightFoundations.md` (file becomes ≈300 LOC).
2. Update syntax (`⟨_, _⟩` for existentials).
3. Re-prove modular arithmetic lemmas with `ZMod 8`.
4. Eliminate all `sorry`s (move long proofs to `formal/` if needed).
5. `lake build foundation.Core.EightFoundations` → 0 errors.

---

## 3  Derivation Modules  (2-3 days)
* For every file in `foundation/Core/Derivations/`:
  1. Keep headline constant.
  2. Provide short Lean proof or mark constant `noncomputable def`.
  3. Delete all `axiom`/`sorry`.

---

## 4  Continuous-Integration Guard  (½ day)
Add `.github/workflows/foundation.yml` that:
* runs `lake build foundation`
* executes `scripts/audit_foundation.py`

CI fails if audit finds any issue.

---

## 5  Tag & Release  (1 hour)
1. When CI green, tag `vFoundation-1.0`.
2. Update README to state foundation is axiom-free.

---

### Timeline / Effort Estimate

| Phase | Effort | ETA |
|-------|--------|-----|
| 0 Audit | 0.5 d | **Day 1 AM** |
| 1 Parameters | 1 d | Day 1 |
| 2 Core | 2 d | Day 3 |
| 3 Derivations | 3 d | Day 6 |
| 4 CI | 0.5 d | Day 6 |
| 5 Tag | 0.1 d | Day 6 |

_Total ≈ 6 developer days._

---

### Immediate Next Action
Begin **Phase 0**: implement `scripts/audit_foundation.py`, run it, commit the proof ledger so we have a definitive baseline before touching any proofs. 