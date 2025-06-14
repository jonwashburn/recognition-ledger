/- 
Theorem: Dual Balance
For any ledger state, the sum of all debits equals the sum of all credits.
-/

theorem dual_balance (s : LedgerState) : total_debit s = total_credit s := by
  -- Get the list of all transactions in the ledger state
  let txns := transactions s
  
  -- By ledger_axioms.valid_transaction, each transaction must balance
  have h1 : ∀ t ∈ txns, transaction_debit t = transaction_credit t := by
    intro t ht
    exact ledger_axioms.transaction_balance t ht

  -- Total debits/credits are sums of individual transaction debits/credits
  have h2 : total_debit s = sum (λ t => transaction_debit t) txns := by
    exact ledger_axioms.total_debit_def
    
  have h3 : total_credit s = sum (λ t => transaction_credit t) txns := by
    exact ledger_axioms.total_credit_def

  -- Since each transaction balances (h1), and totals are sums (h2,h3),
  -- the totals must be equal by sum preservation
  calc total_debit s
    _ = sum (λ t => transaction_debit t) txns := h2
    _ = sum (λ t => transaction_credit t) txns := by
        apply sum_congr
        intro t
        exact h1 t
    _ = total_credit s := h3.symm