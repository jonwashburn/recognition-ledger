/-
Recognition Science - List Partition Helpers
===========================================

Helper lemmas for partitioning and summing lists.
-/

import Mathlib.Data.List.Basic
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

/-- Sum of elements equals sum by counting -/
lemma List.sum_eq_count_sum {α : Type*} [DecidableEq α] [AddCommMonoid β]
  (l : List α) (vals : α → β) :
  l.map vals |>.sum = (l.dedup.map (fun x => (l.count x : β) * vals x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [sum_cons, map_cons]
    -- This requires careful counting logic
    sorry  -- Technical: counting argument

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

end RecognitionScience.Helpers
