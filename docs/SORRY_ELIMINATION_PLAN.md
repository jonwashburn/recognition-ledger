# Sorry-Elimination Master Plan

*Last updated: <!--DATE-->*

---

## 0  Overview
This document captures the high-level technical assessment of the current **Recognition-Science Ethics** code-base and a phased road-map for driving the remaining Lean `sorry` count to **zero**.

The plan is derived from first principles and aligns every pending proof obligation with the eight-axiom foundation.  It supersedes the quick status notes in `ethics/SORRY_STATUS.md`.

---

## 1  Assessment Summary

1. **Conceptual coherence** – Ethics really is derivable from the meta-principle; remaining sorries are implementational.
2. **Technical gaps** fall into four buckets:
   * **A. Structural invariants** (non-negativity, time monotonicity)
   * **B. Book-keeping** (list ordering, projection lemmas)
   * **C. Numeric lemmas** (`Int.floor` / `ℝ` rounding)
   * **D. Virtue/curvature models** (still partially informal)

---

## 2  Canonical First-Principles Decisions

### 2.1  Global invariants to add
```
LedgerState.totals_nonneg    : 0 ≤ totalDebits ∧ 0 ≤ totalCredits
RecognitionDebt.curvature_bound : |ledger.balance| ≤ debt.totalCost.cost - debt.dissipatedCost.cost
```

### 2.2  Reusable numeric lemmas
* `floor_sub_floor`    ⌊x⌋ − ⌊y⌋ ≤ ⌊x−y⌋ ≤ ⌊x⌋ − ⌊y⌋ + 1
* `floor_nonneg_iff`  0 ≤ ⌊x⌋ ↔ 0 ≤ x
* `natAbs_int`         `(n : ℤ).natAbs = |n|`

Will live in `helpers/NumericalTactics.lean`.

### 2.3  Virtue mechanics
Introduce a canonical state
```
structure MoralVector where
  κ  : ℤ   -- curvature
  e  : ℝ≥0 -- stored recognition energy
  φₚ : Fin 8
```
Each `Virtue` becomes a pure function `apply : MoralVector → MoralVector` preserving
```
κ + ⌊e⌋   -- global recognition invariant
```
with golden-ratio parameters exactly matching philosophical claims.

### 2.4  Interaction harmonics
`virtuesHarmonize v₁ v₂` := phase-offset ∈ {0,1,7}.  Harmonising pairs gain φ-enhancement; otherwise they are damped by φ⁻¹.

### 2.5  Curvature from cost (constructive)
```
κ(s) = ⌊ debt.totalCost - debt.dissipatedCost ⌋
```
and
```
κ = 0  ↔  totalCost = dissipatedCost
```
replaces the heavier geometric proof chain.

---

## 3  Phased Road-map

| Phase | Goal | Key Actions | Est. Sorry Δ |
|-------|------|-------------|---------------|
| **0** | Scaffolding | add invariants; helper lemmas | −7 |
| **1** | Virtue core | implement `MoralVector`, generic proofs | −10 |
| **2** | Projection adjunction | prove `toSimpleBalanced ⇄ toRich` round-trip | −5 |
| **3** | Cost ⇢ curvature | adopt constructive lemma, finish `CurvatureFromCost` | −4 |
| **4** | Clean-up & CI | rebuild, set CI to fail at >0 sorries | −remaining |

Projected *post-Phase 3* residual: ≤ 10 intentional philosophical axioms, then 0.

---

## 4  Immediate To-Do (Phase 0)
1. Add `totals_nonneg` & `curvature_bound` to data structures.
2. Create `helpers/NumericalTactics.lean` with floor lemmas & `@[simp]` tags.
3. Propagate non-negativity through `ExtendedLedgerState`, `LedgerAdapter`.
4. Rewrite `toSimpleBalanced` proofs using new lemmas.

Executing these steps should mechanically close 6–7 sorries and lay the groundwork for virtue refactor.

---

> *End of plan.  Subsequent updates should bump the "Last updated" timestamp and append changelog entries.* 