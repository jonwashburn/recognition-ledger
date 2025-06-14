theorem cost_positivity {s : LedgerState} : 
  C_0(s) ≥ 0 ∧ (C_0(s) = 0 ↔ s = vacuum) := by
  -- Split into two parts: non-negativity and vacuum equivalence
  constructor
  
  -- Part 1: Show C_0(s) ≥ 0
  { -- Use ledger_axioms.cost_def which defines C_0 as sum of positive terms
    have h1 := ledger_axioms.cost_def s
    -- Each term in the sum is non-negative by construction
    -- Energy terms E_r are positive by energy_cascade_positive
    -- Multipliers φ^r are positive by golden_ratio_positive
    exact sum_of_nonneg h1 }
    
  -- Part 2: Show C_0(s) = 0 ↔ s = vacuum 
  { constructor
    -- Forward direction: C_0(s) = 0 → s = vacuum
    { intro h2
      -- If sum of non-negative terms is zero, each term must be zero
      have h3 := sum_zero_of_nonneg h2
      -- Only vacuum state has all zero terms by ledger_axioms.vacuum_unique
      exact ledger_axioms.vacuum_unique h3 }
      
    -- Reverse direction: s = vacuum → C_0(s) = 0
    { intro h4
      -- Vacuum state has zero cost by definition
      have h5 := ledger_axioms.vacuum_cost
      rw [h4] at h5
      exact h5 } }