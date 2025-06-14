/-
  IRREDUCIBLE PATTERNS

  This file develops the theory of irreducible patterns in the Recognition
  framework. Irreducible patterns are those that cannot be factored into
  smaller non-trivial patterns.

  Main results:
  - Definition of irreducible patterns
  - Unique factorization theorem for patterns
  - Characterization of irreducibles in terms of atomic structure

  References: Standard factorization theory adapted to free monoids
-/

import Mathlib.Algebra.FreeMonoid
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import RecognitionScience.Pattern.FreeRecognition

namespace RecognitionScience.Pattern

open Pattern

/-!
# Irreducible Patterns

An irreducible pattern is one that cannot be written as a product of two
non-trivial patterns. In the free monoid, these correspond exactly to
the atomic patterns.
-/

/--
  A pattern is irreducible if it is non-trivial and cannot be factored
  into two non-trivial patterns.
-/
def IsIrreducible (p : Pattern) : Prop :=
  p ≠ 1 ∧ ∀ a b : Pattern, p = a * b → a = 1 ∨ b = 1

/--
  A pattern is atomic if it consists of exactly one atomic event.
-/
def IsAtomic (p : Pattern) : Prop :=
  ∃ a : AtomicEvent, p = ofAtom a

/-!
## Basic Properties of Irreducibles
-/

/-- Atomic patterns are irreducible -/
theorem atomic_is_irreducible (p : Pattern) (h : IsAtomic p) : IsIrreducible p := by
  obtain ⟨a, ha⟩ := h
  constructor
  · rw [ha]
    simp [ofAtom]
    intro h_eq
    have : (FreeMonoid.of a).toList = [].toList := by rw [h_eq]
    simp at this
  · intro x y hxy
    rw [ha] at hxy
    -- In a free monoid, if of(a) = x * y, then either x or y must be 1
    have h_list : (FreeMonoid.of a).toList = (x * y).toList := by rw [hxy]
    simp [FreeMonoid.toList_mul] at h_list
    cases' x.toList with hx tx
    · left
      exact FreeMonoid.ext_iff.mpr (by simp)
    · cases' y.toList with hy ty
      · right
        exact FreeMonoid.ext_iff.mpr (by simp)
      · simp at h_list
        have : [a] = hx :: tx ++ hy :: ty := h_list
        simp at this

/-- In a free monoid, irreducible elements are exactly the atomic ones -/
theorem irreducible_iff_atomic (p : Pattern) : IsIrreducible p ↔ IsAtomic p := by
  constructor
  · intro h
    -- If p is irreducible and non-trivial, it must be atomic
    have h_ne_one : p ≠ 1 := h.1
    -- In a free monoid, any non-trivial element can be written as a product of atoms
    -- If it's irreducible, it must be a single atom
    cases' p.toList with head tail
    · simp at h_ne_one
    · cases' tail with head2 tail2
      · -- Single element list - this is atomic
        use head
        exact FreeMonoid.ext_iff.mpr (by simp [ofAtom])
      · -- Multiple elements - this contradicts irreducibility
        exfalso
        let p1 := FreeMonoid.of head
        let p2 := FreeMonoid.ofList (head2 :: tail2)
        have hp : p = p1 * p2 := by
          apply FreeMonoid.ext_iff.mpr
          simp [FreeMonoid.toList_mul, FreeMonoid.ofList]
        have hp1_ne_one : p1 ≠ 1 := by
          simp [p1]
          intro h_eq
          have : (FreeMonoid.of head).toList = [].toList := by rw [h_eq]
          simp at this
        have hp2_ne_one : p2 ≠ 1 := by
          simp [p2, FreeMonoid.ofList]
          intro h_eq
          simp at h_eq
        have := h.2 p1 p2 hp
        cases this with
        | inl h1 => exact hp1_ne_one h1
        | inr h2 => exact hp2_ne_one h2
  · exact atomic_is_irreducible p

/-!
## Unique Factorization
-/

/--
  Every non-trivial pattern has a unique factorization into irreducible patterns.
  In the free monoid, this is just the decomposition into atomic events.
-/
theorem unique_factorization (p : Pattern) (h : p ≠ 1) :
    ∃! factors : List AtomicEvent,
      p = FreeMonoid.ofList factors ∧ factors ≠ [] := by
  use p.toList
  constructor
  · constructor
    · exact FreeMonoid.ofList_toList p
    · intro h_empty
      rw [← List.length_eq_zero] at h_empty
      have : length p = 0 := by simp [length, h_empty]
      have : p = 1 := by
        apply FreeMonoid.ext_iff.mpr
        simp [length] at this
        exact List.eq_nil_of_length_eq_zero this
      exact h this
  · intro factors' ⟨h_eq, h_ne_empty⟩
    have : p.toList = factors' := by
      rw [← FreeMonoid.ofList_toList p, h_eq]
      simp [FreeMonoid.toList_ofList]
    exact this.symm

/--
  The factorization of a pattern into irreducibles is unique up to order.
-/
theorem factorization_unique (p : Pattern) (h : p ≠ 1) :
    ∃! factors : Multiset AtomicEvent,
      p = (factors.toList.map ofAtom).prod ∧ factors ≠ 0 := by
  obtain ⟨factors, h_eq, h_ne_empty⟩ := unique_factorization p h
  use factors.toMultiset
  constructor
  · constructor
    · rw [h_eq]
      simp [FreeMonoid.ofList, List.map_map]
      congr
      ext a
      simp [ofAtom]
    · simp [h_ne_empty]
  · intro factors' ⟨h_eq', h_ne_empty'⟩
    -- Uniqueness follows from the fact that the free monoid has unique factorization
    have h_list : p.toList = factors'.toList.map id := by
      rw [← FreeMonoid.ofList_toList p, h_eq']
      simp [List.prod_map_ofAtom]
    simp at h_list
    rw [← List.toMultiset_inj]
    rw [← h_list]
    simp [List.toMultiset_toList]

/-!
## Properties of Irreducible Patterns
-/

/-- Irreducible patterns have length 1 -/
theorem irreducible_length_one (p : Pattern) (h : IsIrreducible p) : length p = 1 := by
  rw [irreducible_iff_atomic] at h
  obtain ⟨a, ha⟩ := h
  rw [ha, length_ofAtom]

/-- Irreducible patterns have positive grade -/
theorem irreducible_grade_pos (p : Pattern) (h : IsIrreducible p) : 0 < grade p := by
  exact grade_pos_of_ne_one p h.1

/-- The grade of an irreducible pattern equals the atomic cost -/
theorem irreducible_grade (p : Pattern) (h : IsIrreducible p) :
    ∃ a : AtomicEvent, p = ofAtom a ∧ grade p = atomicCost a := by
  rw [irreducible_iff_atomic] at h
  obtain ⟨a, ha⟩ := h
  use a
  constructor
  · exact ha
  · rw [ha, grade_ofAtom]

/-!
## Decidability
-/

/-- It is decidable whether a pattern is irreducible -/
instance (p : Pattern) : Decidable (IsIrreducible p) := by
  rw [irreducible_iff_atomic]
  -- Check if the pattern's list representation has exactly one element
  cases' p.toList with head tail
  · -- Empty list - not atomic
    exact decidable_of_iff False (by simp [IsAtomic, ofAtom])
  · cases' tail with head2 tail2
    · -- Single element - atomic
      exact decidable_of_iff True (by
        simp [IsAtomic]
        use head
        exact FreeMonoid.ext_iff.mpr (by simp [ofAtom]))
    · -- Multiple elements - not atomic
      exact decidable_of_iff False (by
        simp [IsAtomic, ofAtom]
        intro a h_eq
        have : (FreeMonoid.of a).toList = (head :: head2 :: tail2) := by rw [h_eq]
        simp at this)

/-!
## Enumeration of Irreducibles
-/

/-- The set of irreducible patterns with grade at most n -/
def irreducibles_bounded_grade (n : ℝ≥0) : Set Pattern :=
  {p | IsIrreducible p ∧ grade p ≤ n}

/-- This set is finite -/
theorem finite_irreducibles_bounded_grade (n : ℝ≥0) :
    (irreducibles_bounded_grade n).Finite := by
  -- Irreducible patterns are atomic, so we just need to count atomic events
  -- with cost at most n
  have h_subset : irreducibles_bounded_grade n ⊆
    (Set.range ofAtom) ∩ {p | grade p ≤ n} := by
    intro p hp
    constructor
    · rw [irreducible_iff_atomic] at hp.1
      exact Set.mem_range_of_exists hp.1
    · exact hp.2
  apply Set.Finite.subset _ h_subset
  -- The intersection is finite because there are only finitely many
  -- atomic events with cost ≤ n (since atomicCost is constant 1)
  have h_finite_atoms : {a : AtomicEvent | atomicCost a ≤ n}.Finite := by
    -- Since atomicCost a = 1 for all a, this is either empty (if n < 1) or all of ℕ
    by_cases h : n < 1
    · simp [Set.setOf_false]
      exact Set.finite_empty
    · -- If n ≥ 1, then all atomic events satisfy the bound, but we need finiteness
      -- This is where we'd need additional structure on atomic events
      sorry -- This requires bounding the atomic events somehow
  exact Set.Finite.image ofAtom h_finite_atoms

/-!
## Generators
-/

/-- Every pattern can be written as a product of irreducible patterns -/
theorem pattern_factorization (p : Pattern) :
    ∃ factors : List Pattern,
      (∀ q ∈ factors, IsIrreducible q) ∧ p = factors.prod := by
  induction p using pattern_induction with
  | h_one =>
    use []
    simp
  | h_atom a =>
    use [ofAtom a]
    constructor
    · intro q hq
      simp at hq
      rw [hq]
      rw [irreducible_iff_atomic]
      use a
    · simp
  | h_mul p q ihp ihq =>
    obtain ⟨factors_p, h_irred_p, h_eq_p⟩ := ihp
    obtain ⟨factors_q, h_irred_q, h_eq_q⟩ := ihq
    use factors_p ++ factors_q
    constructor
    · intro r hr
      simp at hr
      cases hr with
      | inl h => exact h_irred_p r h
      | inr h => exact h_irred_q r h
    · rw [List.prod_append, h_eq_p, h_eq_q]

/-- The irreducible patterns generate the entire pattern monoid -/
theorem irreducibles_generate :
    Submonoid.closure (Set.range ofAtom) = ⊤ := by
  ext p
  simp [Submonoid.mem_closure_iff]
  constructor
  · intro h
    trivial
  · intro h
    obtain ⟨factors, h_irred, h_eq⟩ := pattern_factorization p
    rw [← h_eq]
    apply List.prod_mem
    intro q hq
    have h_irred_q := h_irred q hq
    rw [irreducible_iff_atomic] at h_irred_q
    obtain ⟨a, ha⟩ := h_irred_q
    rw [ha]
    exact Set.mem_range_self a

end RecognitionScience.Pattern
