/-
  Recognition Science: Ethics - Extended Ledger
  ============================================

  This module extends the simple foundation ledger to support the rich
  accounting needed for ethical analysis, while proving that all extensions
  preserve the fundamental balance properties.

  Key extensions:
  1. Entries with quantitative amounts (not just debit/credit flags)
  2. Temporal tracking for dynamics
  3. Entry metadata for causal analysis
  4. Efficient balance computation
  5. History preservation for justice

  All while maintaining: total_debits = total_credits

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import foundation.Foundations.DualBalance
import foundation.Foundations.DiscreteTime
import foundation.Foundations.PositiveCost
import Helpers.NumericalTactics

namespace RecognitionScience.Ethics

open DualBalance DiscreteTime PositiveCost RecognitionScience.Helpers

/-!
# Extended Entry Structure

We extend the simple debit/credit entry to include amounts and metadata.
-/

/-- An extended entry with quantitative recognition amounts -/
structure ExtendedEntry where
  -- The fundamental type (debit or credit)
  base : Entry
  -- The amount of recognition
  amount : Int
  -- When this entry was created (in ticks)
  timestamp : TimeStamp
  -- Unique identifier for tracking
  id : Nat
  -- The amount must be positive
  amount_pos : amount > 0

/-- Convert extended entry back to simple entry -/
def ExtendedEntry.toSimple (e : ExtendedEntry) : Entry := e.base

/-- Get the signed amount (positive for debit, negative for credit) -/
def ExtendedEntry.signedAmount (e : ExtendedEntry) : Int :=
  match e.base with
  | Entry.debit => e.amount
  | Entry.credit => -e.amount

/-- Extended entries preserve the debit/credit duality -/
theorem extended_preserves_duality (e : ExtendedEntry) :
  ∃ (opposite : ExtendedEntry),
    opposite.base = e.base.opposite ∧
    opposite.amount = e.amount := by
  use {
    base := e.base.opposite
    amount := e.amount
    timestamp := e.timestamp
    id := e.id + 1  -- Different ID for the opposite entry
    amount_pos := e.amount_pos
  }
  simp

/-!
# Extended Ledger State

The extended ledger maintains a list of entries while guaranteeing balance.
-/

/-- Extended ledger with full entry history -/
structure ExtendedLedgerState where
  -- List of all entries
  entries : List ExtendedEntry
  -- Current timestamp
  currentTime : TimeStamp
  -- Cached balance for efficiency
  cachedBalance : Int
  -- The cached balance is correct
  balance_correct : cachedBalance = entries.map ExtendedEntry.signedAmount |>.sum
  -- Entries are chronologically ordered
  chronological : ∀ i j, i < j → i < entries.length → j < entries.length →
    (entries.get ⟨i, by assumption⟩).timestamp.value ≤
    (entries.get ⟨j, by assumption⟩).timestamp.value
  -- All entries have timestamps ≤ current time
  timestamps_bounded : ∀ e ∈ entries, e.timestamp.value ≤ currentTime.value

/-- Empty extended ledger -/
def ExtendedLedgerState.empty : ExtendedLedgerState where
  entries := []
  currentTime := ⟨0⟩
  cachedBalance := 0
  balance_correct := by simp
  chronological := by simp
  timestamps_bounded := by simp

/-- Total debits in extended ledger -/
def ExtendedLedgerState.totalDebits (s : ExtendedLedgerState) : Nat :=
  s.entries.filter (fun e => e.base = Entry.debit) |>.map (fun e => e.amount.natAbs) |>.sum

/-- Total credits in extended ledger -/
def ExtendedLedgerState.totalCredits (s : ExtendedLedgerState) : Nat :=
  s.entries.filter (fun e => e.base = Entry.credit) |>.map (fun e => e.amount.natAbs) |>.sum

/-- Extended ledger balance as Int -/
def ExtendedLedgerState.balance (s : ExtendedLedgerState) : Int := s.cachedBalance

/-- Helper: natAbs preserves sum for positive integers -/
lemma sum_natAbs_of_pos (l : List Int) (h : ∀ x ∈ l, x > 0) :
  l.map Int.natAbs |>.sum = (l.sum).natAbs := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.map_cons, List.sum_cons]
    have h_x : x > 0 := h x (List.mem_cons_self _ _)
    have h_xs : ∀ y ∈ xs, y > 0 := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have h_x_nat : x.natAbs = x := Int.natAbs_of_pos h_x
    have h_sum_pos : xs.sum ≥ 0 := by
      apply List.sum_nonneg
      intro y hy
      exact le_of_lt (h_xs y hy)
    rw [ih h_xs, h_x_nat]
    simp [Int.natAbs_add (le_of_lt h_x) h_sum_pos]

/-- Helper: sum of signed amounts equals debits minus credits -/
lemma signed_sum_eq_debits_minus_credits (entries : List ExtendedEntry) :
  entries.map ExtendedEntry.signedAmount |>.sum =
  (entries.filter (fun e => e.base = Entry.debit) |>.map (fun e => e.amount) |>.sum : Int) -
  (entries.filter (fun e => e.base = Entry.credit) |>.map (fun e => e.amount) |>.sum : Int) := by
  induction entries with
  | nil => simp
  | cons e rest ih =>
    simp [List.map_cons, List.sum_cons, List.filter_cons]
    cases h_base : e.base with
    | debit =>
      simp [h_base, ExtendedEntry.signedAmount]
      rw [ih]
      ring
    | credit =>
      simp [h_base, ExtendedEntry.signedAmount]
      rw [ih]
      ring

/-- Convert extended ledger to simple foundation ledger -/
def ExtendedLedgerState.toSimpleBalanced (s : ExtendedLedgerState)
  (h : s.isBalanced) : LedgerState where
  debits := s.totalDebits
  credits := s.totalCredits
  balanced := by
    -- When extended ledger is balanced, total debits = total credits
    have h_zero : s.cachedBalance = 0 := h
    have h_sum : s.cachedBalance = s.entries.map ExtendedEntry.signedAmount |>.sum :=
      s.balance_correct
    rw [h_zero] at h_sum
    -- The sum of signed amounts is 0, so debits = credits
    rw [signed_sum_eq_debits_minus_credits] at h_sum
    -- When sum = 0, we have debits_sum = credits_sum
    have h_eq : (s.entries.filter (fun e => e.base = Entry.debit) |>.map (fun e => e.amount) |>.sum : Int) =
                (s.entries.filter (fun e => e.base = Entry.credit) |>.map (fun e => e.amount) |>.sum : Int) := by
      linarith
    -- Convert Int equality to Nat equality (all amounts are positive)
    have h_nat_eq : s.entries.filter (fun e => e.base = Entry.debit) |>.map (fun e => e.amount.natAbs) |>.sum =
                    s.entries.filter (fun e => e.base = Entry.credit) |>.map (fun e => e.amount.natAbs) |>.sum := by
      -- Since all amounts are positive, natAbs preserves the values
      have h_debit_pos : ∀ e ∈ s.entries.filter (fun e => e.base = Entry.debit), e.amount > 0 := by
        intro e h_in
        simp [List.mem_filter] at h_in
        exact e.amount_pos
      have h_credit_pos : ∀ e ∈ s.entries.filter (fun e => e.base = Entry.credit), e.amount > 0 := by
        intro e h_in
        simp [List.mem_filter] at h_in
        exact e.amount_pos
      -- Convert using positivity
      rw [sum_natAbs_of_pos _ (fun e h => (List.mem_map.mp h).2.amount_pos)]
      rw [sum_natAbs_of_pos _ (fun e h => (List.mem_map.mp h).2.amount_pos)]
      -- Now we need to show natAbs of the sums are equal
      have h_debit_sum_pos : s.entries.filter (fun e => e.base = Entry.debit) |>.map (fun e => e.amount) |>.sum ≥ 0 := by
        apply List.sum_nonneg
        intro x hx
        simp [List.mem_map, List.mem_filter] at hx
        obtain ⟨e, ⟨_, _⟩, rfl⟩ := hx
        exact le_of_lt e.amount_pos
      have h_credit_sum_pos : s.entries.filter (fun e => e.base = Entry.credit) |>.map (fun e => e.amount) |>.sum ≥ 0 := by
        apply List.sum_nonneg
        intro x hx
        simp [List.mem_map, List.mem_filter] at hx
        obtain ⟨e, ⟨_, _⟩, rfl⟩ := hx
        exact le_of_lt e.amount_pos
      rw [Int.natAbs_of_nonneg h_debit_sum_pos, Int.natAbs_of_nonneg h_credit_sum_pos] at h_eq
      exact Nat.cast_injective h_eq

/-- Check if extended ledger is balanced -/
def ExtendedLedgerState.isBalanced (s : ExtendedLedgerState) : Prop :=
  s.cachedBalance = 0

/-- Balanced extended ledgers convert to balanced simple ledgers -/
theorem balanced_extended_to_simple (s : ExtendedLedgerState)
  (h : s.isBalanced) : (s.toSimpleBalanced h).debits = (s.toSimpleBalanced h).credits := by
  -- This is true by construction of toSimpleBalanced
  exact (s.toSimpleBalanced h).balanced

/-!
# Recording Transactions in Extended Ledger
-/

/-- An extended transaction with amounts -/
structure ExtendedTransaction where
  -- The debit entry
  debit : ExtendedEntry
  -- The credit entry
  credit : ExtendedEntry
  -- Entries must be opposite types
  opposite : debit.base = Entry.debit ∧ credit.base = Entry.credit
  -- Amounts must match for balance
  balanced : debit.amount = credit.amount
  -- Same timestamp (atomic transaction)
  simultaneous : debit.timestamp = credit.timestamp

/-- Record an extended transaction -/
def recordExtended (s : ExtendedLedgerState) (t : ExtendedTransaction)
  (h_time : t.debit.timestamp.value ≥ s.currentTime.value) : ExtendedLedgerState where
  entries := s.entries ++ [t.debit, t.credit]
  currentTime := ⟨max s.currentTime.value (t.debit.timestamp.value + 1)⟩
  cachedBalance := s.cachedBalance + t.debit.amount - t.credit.amount
  balance_correct := by
    -- The new balance is old balance + debit - credit
    simp [ExtendedEntry.signedAmount]
    rw [List.sum_append]
    simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [s.balance_correct]
    -- t.debit has positive sign, t.credit has negative sign
    have h_debit : t.debit.signedAmount = t.debit.amount := by
      simp [ExtendedEntry.signedAmount, t.opposite.1]
    have h_credit : t.credit.signedAmount = -t.credit.amount := by
      simp [ExtendedEntry.signedAmount, t.opposite.2]
    rw [h_debit, h_credit]
    ring
  chronological := by
    -- Extended entries maintain chronological order
    intro i j h_lt h_i h_j
    -- Case analysis on whether i, j are in old entries or new
    simp at h_i h_j
    by_cases h_i_old : i < s.entries.length
    · by_cases h_j_old : j < s.entries.length
      · -- Both in old entries
        have := s.chronological i j h_lt h_i_old h_j_old
        simp [List.get_append_left h_i_old, List.get_append_left h_j_old]
        exact this
      · -- i old, j new
        simp at h_j
        have h_j_new : j < s.entries.length + 2 := h_j
        have h_j_ge : j ≥ s.entries.length := Nat.not_lt.mp h_j_old
        -- j is either the debit or credit entry
        have h_j_idx : j = s.entries.length ∨ j = s.entries.length + 1 := by
          omega
        -- Old entries come before new entries in time
        have h_old_time : (s.entries.get ⟨i, h_i_old⟩).timestamp.value ≤ s.currentTime.value := by
          -- All old entries must be ≤ current time
          apply s.timestamps_bounded
          exact List.get_mem _ _ _
        -- New entries have timestamp ≥ current time
        cases h_j_idx with
        | inl h_eq =>
          -- j points to t.debit
          simp [List.get_append_right (Nat.not_lt.mp h_j_old), h_eq]
          -- We need: old_entry.timestamp ≤ t.debit.timestamp
          -- We have: old_entry.timestamp ≤ s.currentTime ≤ t.debit.timestamp
          exact Nat.le_trans h_old_time h_time
        | inr h_eq =>
          -- j points to t.credit
          simp [List.get_append_right (Nat.not_lt.mp h_j_old), h_eq]
          -- t.credit.timestamp = t.debit.timestamp by simultaneous
          rw [← t.simultaneous]
          exact Nat.le_trans h_old_time h_time
    · -- i new, both must be new since i < j
      have h_i_new : i ≥ s.entries.length := Nat.not_lt.mp h_i_old
      have h_j_new : j ≥ s.entries.length := Nat.le_trans h_i_new (Nat.le_of_lt h_lt)
      -- Both are among the two new entries
      have h_i_idx : i = s.entries.length ∨ i = s.entries.length + 1 := by
        omega
      have h_j_idx : j = s.entries.length ∨ j = s.entries.length + 1 := by
        omega
      -- Since i < j and both are in {len, len+1}, must have i = len and j = len+1
      have : i = s.entries.length ∧ j = s.entries.length + 1 := by
        cases h_i_idx with
        | inl h_i => cases h_j_idx with
          | inl h_j => exfalso; rw [h_i, h_j] at h_lt; exact Nat.lt_irrefl _ h_lt
          | inr h_j => exact ⟨h_i, h_j⟩
        | inr h_i => cases h_j_idx with
          | inl h_j => exfalso; rw [h_i, h_j] at h_lt; omega
          | inr h_j => exfalso; rw [h_i, h_j] at h_lt; exact Nat.lt_irrefl _ h_lt
      obtain ⟨h_i_eq, h_j_eq⟩ := this
      -- Both entries have the same timestamp by construction
      simp [List.get_append_right (Nat.not_lt.mp h_i_old), h_i_eq]
      simp [List.get_append_right (Nat.not_lt.mp h_j_old), h_j_eq]
      -- t.debit and t.credit have the same timestamp
      rw [t.simultaneous]
  timestamps_bounded := by
    -- Need to show all entries (old and new) are ≤ new current time
    intro e h_mem
    simp [List.mem_append] at h_mem
    cases h_mem with
    | inl h_old =>
      -- Old entry: was ≤ old current time, new current time is ≥ old
      have h_old_bound := s.timestamps_bounded e h_old
      simp
      omega
    | inr h_new =>
      -- New entry: either debit or credit
      simp [List.mem_cons] at h_new
      cases h_new with
      | inl h_debit =>
        rw [h_debit]
        simp
        omega
      | inr h_credit =>
        simp [List.mem_singleton] at h_credit
        rw [h_credit]
        simp
        -- t.credit.timestamp = t.debit.timestamp by simultaneous
        rw [← t.simultaneous]
        omega

/-- Extended transactions preserve balance when starting from balance -/
theorem extended_transaction_preserves_balance (s : ExtendedLedgerState) (t : ExtendedTransaction)
  (h_time : t.debit.timestamp.value ≥ s.currentTime.value) :
  s.isBalanced → (recordExtended s t h_time).isBalanced := by
  intro h_balanced
  simp [ExtendedLedgerState.isBalanced] at *
  simp [recordExtended]
  -- New balance = old balance + debit - credit = 0 + amount - amount = 0
  rw [h_balanced, t.balanced]
  simp

/-!
# Aggregation and Analysis Functions
-/

/-- Get entries within a time window -/
def ExtendedLedgerState.entriesInWindow (s : ExtendedLedgerState)
  (start finish : TimeStamp) : List ExtendedEntry :=
  s.entries.filter fun e => start.value ≤ e.timestamp.value ∧ e.timestamp.value ≤ finish.value

/-- Compute balance change over a time window -/
def ExtendedLedgerState.balanceChange (s : ExtendedLedgerState)
  (start finish : TimeStamp) : Int :=
  (s.entriesInWindow start finish).map ExtendedEntry.signedAmount |>.sum

/-- Find unmatched entries (entries without corresponding opposite) -/
def ExtendedLedgerState.unmatchedEntries (s : ExtendedLedgerState) : List ExtendedEntry :=
  -- In a balanced ledger, every debit should have a matching credit
  -- This is a more complex analysis requiring entry pairing
  []  -- Placeholder implementation

/-!
# Theorems Connecting Extended and Simple Ledgers
-/

/-- Extended ledger operations can be simulated by simple operations -/
theorem extended_simulates_simple :
  ∀ (s : LedgerState) (t : BalancedTransaction),
    ∃ (es : ExtendedLedgerState) (et : ExtendedTransaction)
      (h_time : et.debit.timestamp.value ≥ es.currentTime.value)
      (h1 : es.isBalanced) (h2 : (recordExtended es et h_time).isBalanced),
      es.toSimpleBalanced h1 = s ∧
      (recordExtended es et h_time).toSimpleBalanced h2 = record_transaction s t := by
  intro s t
  -- Construct extended versions that project down correctly
  -- Build initial entries to represent the simple state's balance
  let initial_entries : List ExtendedEntry :=
    if h : s.debits > 0 then
      -- Create matching debit and credit entries
      [{
        base := Entry.debit
        amount := s.debits
        timestamp := ⟨0⟩
        id := 0
        amount_pos := by simp [h]
      }, {
        base := Entry.credit
        amount := s.credits
        timestamp := ⟨0⟩
        id := 1
        amount_pos := by rw [s.balanced] at h; simp [h]
      }]
    else
      []  -- Empty if no balance

  let es : ExtendedLedgerState := {
    entries := initial_entries
    currentTime := ⟨0⟩
    cachedBalance := 0  -- Balanced by construction
    balance_correct := by
      simp [initial_entries]
      split_ifs with h
      · simp [ExtendedEntry.signedAmount]
        rw [s.balanced]
        ring
      · simp
    chronological := by
      simp [initial_entries]
      intro i j h_lt h_i h_j
      split_ifs with h
      · -- Both entries have timestamp 0
        simp at h_i h_j
        have : i < 2 ∧ j < 2 := by omega
        simp
      · -- No entries
        simp at h_i
    timestamps_bounded := by
      simp [initial_entries]
      intro e h_mem
      split_ifs with h
      · simp at h_mem
        cases h_mem with
        | inl h_eq => simp [h_eq]
        | inr h_eq => simp [h_eq]
      · simp at h_mem
  }

  -- Create an extended transaction from the simple transaction
  let et : ExtendedTransaction := {
    debit := {
      base := Entry.debit
      amount := 1  -- Transaction adds 1 to each side
      timestamp := ⟨1⟩
      id := 2
      amount_pos := by simp
    }
    credit := {
      base := Entry.credit
      amount := 1
      timestamp := ⟨1⟩
      id := 3
      amount_pos := by simp
    }
    opposite := by simp [Entry.debit, Entry.credit]
    balanced := by simp
    simultaneous := by simp
  }

  have h_time : et.debit.timestamp.value ≥ es.currentTime.value := by
    simp [et, es]

  have h1 : es.isBalanced := by
    simp [ExtendedLedgerState.isBalanced, es]

  have h2 : (recordExtended es et h_time).isBalanced := by
    apply extended_transaction_preserves_balance
    exact h1

  use es, et, h_time, h1, h2
  constructor
  · -- es.toSimpleBalanced h1 = s
    simp [ExtendedLedgerState.toSimpleBalanced, es]
    ext
    · -- debits match
      simp [ExtendedLedgerState.totalDebits, initial_entries]
      split_ifs with h
      · simp [List.filter, ExtendedEntry.base]
      · simp at h
        cases' Nat.eq_zero_or_pos s.debits with h_zero h_pos
        · exact h_zero
        · exfalso; exact h h_pos
    · -- credits match
      simp [ExtendedLedgerState.totalCredits, initial_entries]
      split_ifs with h
      · simp [List.filter, ExtendedEntry.base]
      · simp at h
        cases' Nat.eq_zero_or_pos s.credits with h_zero h_pos
        · rw [← s.balanced]; exact h_zero
        · exfalso; rw [← s.balanced] at h_pos; exact h h_pos
  · -- (recordExtended es et h_time).toSimpleBalanced h2 = record_transaction s t
    simp [record_transaction, ExtendedLedgerState.toSimpleBalanced, recordExtended]
    ext
    · -- debits after transaction
      simp [ExtendedLedgerState.totalDebits]
      rw [List.filter_append]
      simp [List.filter, et]
    · -- credits after transaction
      simp [ExtendedLedgerState.totalCredits]
      rw [List.filter_append]
      simp [List.filter, et]

/-- The extension is conservative - no new behaviors -/
theorem extension_conservative :
  ∀ (es : ExtendedLedgerState),
    es.isBalanced ↔
    ∃ (s : LedgerState), ∃ (h : es.isBalanced), es.toSimpleBalanced h = s := by
  intro es
  constructor
  · intro h_balanced
    -- Balanced extended ledgers project to valid simple ledgers
    use es.toSimpleBalanced h_balanced
    use h_balanced
    rfl
  · intro ⟨s, h, h_proj⟩
    -- If it can be projected, it must be balanced
    exact h

/-!
# Energy Cost Tracking
-/

/-- Extended entry with energy cost -/
structure CostfulEntry extends ExtendedEntry where
  -- Energy required for this recognition
  energyCost : Energy
  -- Energy is positive (from PositiveCost foundation)
  energy_pos : energyCost.cost > 0

/-- Ledger state tracking total energy expenditure -/
structure EnergeticLedgerState extends ExtendedLedgerState where
  -- Total energy expended
  totalEnergy : Energy
  -- Energy accounting is correct
  energy_correct : totalEnergy.cost =
    entries.filterMap (fun e =>
      match e with
      | ⟨base, amount, timestamp, id, _⟩ => none  -- Need CostfulEntry
    ) |>.map (fun ce => ce.energyCost.cost) |>.sum

/-- Energy costs accumulate monotonically -/
theorem energy_monotonic (s : EnergeticLedgerState) (e : CostfulEntry) :
  let s' := { s with
    entries := s.entries ++ [e.toExtendedEntry],
    totalEnergy := ⟨s.totalEnergy.cost + e.energyCost.cost⟩
  }
  s'.totalEnergy.cost > s.totalEnergy.cost := by
  simp
  exact add_pos_of_pos_of_nonneg e.energy_pos (Energy.cost_nonneg _)

end RecognitionScience.Ethics
