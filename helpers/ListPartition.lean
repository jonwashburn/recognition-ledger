/-
Recognition Science - List Partition Helpers
===========================================

Helper lemmas for partitioning and summing lists.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Group.List

namespace RecognitionScience.Helpers

open List

/-!
## List Partition and Sum Lemmas
-/

/-- Summing over a filtered list plus its complement equals the total sum -/
lemma List.sum_filter_partition {α : Type*} [AddCommMonoid α]
  (l : List α) (p : α → Bool) (f : α → α) :
  (l.filter p).foldl (fun acc x => acc + f x) 0 +
  (l.filter (fun x => !p x)).foldl (fun acc x => acc + f x) 0 =
  l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x
    · simp [h, ih, add_assoc, add_comm]
    · simp [h, ih, add_assoc, add_comm]

/-- Three-way partition equals two consecutive two-way partitions -/
lemma List.three_way_partition {α : Type*} [AddCommMonoid α]
  (l : List α) (p q : α → Bool) (f : α → α) :
  let part1 := l.filter p
  let part2 := l.filter (fun x => !p x && q x)
  let part3 := l.filter (fun x => !p x && !q x)
  part1.foldl (fun acc x => acc + f x) 0 +
  part2.foldl (fun acc x => acc + f x) 0 +
  part3.foldl (fun acc x => acc + f x) 0 =
  l.foldl (fun acc x => acc + f x) 0 := by
  -- First partition by p
  have h1 := sum_filter_partition l p f
  -- Then partition the !p part by q
  have h2 := sum_filter_partition (l.filter (fun x => !p x)) q f
  -- Combine the results
  simp only [filter_filter] at h2
  rw [←h1, ←h2]
  simp [add_assoc]

/-- The sum of a function over a list equals the sum over deduplicated elements weighted by count -/
-- Note: Changed from multiplication to scalar multiplication (nsmul)
lemma List.sum_eq_count_sum {α β : Type*} [DecidableEq α] [AddCommMonoid β]
  (l : List α) (vals : α → β) :
  l.map vals |>.sum = (l.dedup.map (fun x => (l.count x) • vals x)).sum := by
  -- Convert to multiset for easier manipulation
  have h_multiset : l.map vals |>.sum = (l.toMultiset.map vals).sum := by
    simp [Multiset.sum_coe]
  -- Key insight: grouping by multiplicity
  -- For each x in dedup, it contributes count(x) * vals(x) to the sum
  rw [h_multiset]
  -- Convert RHS to multiset
  have h_rhs : (l.dedup.map (fun x => (l.count x) • vals x)).sum =
    (l.dedup.toMultiset.map (fun x => (l.count x) • vals x)).sum := by
    simp [Multiset.sum_coe]
  rw [h_rhs]
  -- The key lemma: sum over multiset equals sum over support with multiplicities
  -- This is Multiset.sum_map_count_eq or similar
  simp only [List.toMultiset_map, List.count_toMultiset]
  -- Use that dedup gives exactly the support elements
  have : l.dedup.toMultiset = l.toMultiset.toFinset.val := by
    ext x
    simp [List.count_dedup, Multiset.count_toFinset]
    by_cases h : x ∈ l
    · simp [h, List.count_pos]
    · simp [h, List.count_eq_zero_of_not_mem]
  rw [this]
  -- Now use the standard multiset sum formula
  convert Multiset.sum_map_count_smul_eq (l.toMultiset) vals
  simp

/-- Filtering preserves ordering -/
lemma List.filter_sorted {α : Type*} [LinearOrder α]
  (l : List α) (p : α → Bool) :
  l.Sorted (· < ·) → (l.filter p).Sorted (· < ·) := by
  intro h_sorted
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases h_sorted with
    | nil => simp
    | cons h_head h_tail =>
      by_cases hp : p x
      · simp [hp]
        constructor
        · intro y hy
          simp at hy
          obtain ⟨hy_mem, hy_p⟩ := hy
          exact h_head y hy_mem
        · exact ih h_tail
      · simp [hp]
        exact ih h_tail

-- Count of partitions
theorem partitions_count (l : List α) (p : ListPartition l) :
    p.parts.length = p.parts.length := by
  -- This is trivially true by reflexivity
  -- The actual interesting theorem would relate length to some property
  -- For example: ∑ part.length over parts = l.length
  -- But as stated, this is just reflexivity
  rfl

-- The more meaningful theorem about partition lengths
theorem partition_length_sum (l : List α) (p : ListPartition l) :
    (p.parts.map List.length).sum = l.length := by
  -- Convert to multiset equality and use length preservation
  have h_union := p.parts_union
  -- Taking length of both sides of the multiset equality
  have h_lengths : (Multiset.ofList l).card =
    (p.parts.map (fun part => (Multiset.ofList part))).sum.card := by
    rw [← h_union]
  -- Card of list multiset is list length
  simp [Multiset.card_ofList] at h_lengths
  -- Card of sum is sum of cards
  rw [Multiset.card_sum] at h_lengths
  -- Simplify map operations
  convert h_lengths
  ext part
  simp [Multiset.card_ofList]

end RecognitionScience.Helpers
