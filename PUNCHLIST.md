# Recognition-Ledger Punch-List

_Last updated: 2025-06-26_

This file tracks the remaining open items needed to drive the **main** Lean codebase to a fully proof-complete, maintainer-friendly state.

>  ✔ = done  □ = still to do

---

## 1  Open `sorry`s in the production tree (non-ethics, non-backups)

- [ ] **helpers/InfoTheory.lean**  
  □ Prove/replace `Real.rpow` monotonicity lemma used in φ vs n^(1/n).

- [ ] **helpers/Helpers/InfoTheory.lean**  
  □ Formalise _cost sub-additivity_ (replace placeholder axiom with either a real proof or a properly documented axiom in a dedicated file).  
  □ Reuse the `Real.rpow` monotonicity result here (decreasing n^(1/n)).  
  □ Finish the edge-case analysis for `1 < a < 1.1` in `exp_dominates_nat` so the proof no longer defers to a comment.

Once the four bullets above are solved, the **main library will compile with zero `sorry`s**.

---

## 2  Deep analytic proofs (optional for zero-sorry target)

These files no longer have Lean holes but still contain commented "requires …" blocks that mark places where full formal proofs would live.

- **formal/Variational.lean**  
  □ Leibniz-rule proof for `first_variation`.  
  □ Construct explicit bump functions for the fundamental lemma.  
  □ Integral-monotonicity lemma in `least_action_recognition`.  
  □ Noether conserved-quantity proof (differential-geometry machinery).

You may decide to leave these as documented future work or move them to a research branch.

---

## 3  Numeric placeholder stubs

_These do not block a clean build but we may eventually want computer-checked bounds._

- **formal/EightTickWeinberg.lean** – replace "Numerical computation" comments with `norm_num`/`interval_cases` evaluations (sin², tan, cos approximations).
- **gravity/Quantum/BornRule.lean** – finalise limit proofs currently explained informally.
- **gravity/Quantum/BandwidthCost.lean** – finish Jensen-inequality argument for criticality.

---

## 4  Repository housekeeping

- [ ] Prune or archive the large `backups/` and `AI Solver/` trees (they contain hundreds of stale `sorry`s).  
  Recommendation: move them under `.archive/` and remove from `lakefile` path so they do not appear in ordinary builds.
- [ ] Delete removed/renamed files still tracked in Git history if no longer needed (`ParticleMassesRevised.lean`, `SORRY_RESOLUTION_STATUS.md`, old test files, etc.).

---

### How we will work this list

1. Keep this document up to date—check off items or add notes in each PR.  
2. When an item is completed, mark its checkbox and include a link to the commit.
3. Re-order tasks as priorities shift.

Happy proving! 