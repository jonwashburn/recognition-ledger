theorem eight_beat_closure {s : LedgerState} : commutes (L^8 s) J := by
  -- First establish basic properties from ledger axioms
  have h1 : ∀ s, L (J s) = J (L s) := by
    apply ledger_axioms.commute_LJ
    
  -- Show commutation for power of 8 using induction
  have h2 : ∀ n, n ≤ 8 → commutes (L^n s) J := by
    intro n hn
    induction n with
    | zero => simp [commutes]
    | succ n ih =>
      simp [pow_succ, commutes]
      rw [h1]
      exact ih (nat.le_of_succ_le hn)

  -- Apply to specific case of n=8
  exact h2 8 (by refl)

where
  commutes (x y : LedgerState) := x = y