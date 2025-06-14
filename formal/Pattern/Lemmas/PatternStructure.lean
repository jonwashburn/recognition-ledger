/-
  PATTERN STRUCTURE LEMMAS

  Small lemmas about pattern monoid structure.
-/

import RecognitionScience.Pattern.FreeRecognition
import RecognitionScience.Pattern.Irreducible
import RecognitionScience.Pattern.Lemmas.BasicInequalities

namespace RecognitionScience.Pattern.Lemmas

open Pattern

-- Pattern equality

lemma pattern_eq_one_iff_length_zero (p : Pattern) :
  p = 1 ↔ length p = 0 := by sorry

lemma pattern_ne_one_iff_length_pos (p : Pattern) :
  p ≠ 1 ↔ 0 < length p := by sorry

lemma pattern_eq_iff_toList_eq (p q : Pattern) :
  p = q ↔ p.toList = q.toList := by sorry

-- Pattern multiplication

lemma mul_comm_pattern (p q : Pattern) : p * q = q * p := by sorry

lemma mul_assoc_pattern (p q r : Pattern) :
  (p * q) * r = p * (q * r) := by sorry

lemma one_mul_pattern (p : Pattern) : 1 * p = p := by sorry

lemma mul_one_pattern (p : Pattern) : p * 1 = p := by sorry

-- Grade properties

lemma grade_eq_zero_iff (p : Pattern) : grade p = 0 ↔ p = 1 := by sorry

lemma grade_pos_iff (p : Pattern) : 0 < grade p ↔ p ≠ 1 := by sorry

lemma grade_le_length (p : Pattern) : grade p ≤ length p := by sorry

lemma grade_eq_length_iff (p : Pattern) :
  grade p = length p ↔ ∀ a ∈ p.toList, atomicCost a = 1 := by sorry

-- Atomic patterns

lemma ofAtom_ne_one (a : AtomicEvent) : ofAtom a ≠ 1 := by sorry

lemma ofAtom_injective : Function.Injective ofAtom := by sorry

lemma ofAtom_eq_iff (a b : AtomicEvent) :
  ofAtom a = ofAtom b ↔ a = b := by sorry

lemma length_ofAtom_eq_one (a : AtomicEvent) :
  length (ofAtom a) = 1 := by sorry

-- Irreducibility

lemma irreducible_iff_length_one (p : Pattern) :
  IsIrreducible p ↔ length p = 1 := by sorry

lemma irreducible_ofAtom (a : AtomicEvent) :
  IsIrreducible (ofAtom a) := by sorry

lemma not_irreducible_one : ¬IsIrreducible 1 := by sorry

lemma not_irreducible_mul {p q : Pattern}
  (hp : p ≠ 1) (hq : q ≠ 1) : ¬IsIrreducible (p * q) := by sorry

-- Pattern decomposition

lemma exists_atomic_factor {p : Pattern} (h : p ≠ 1) :
  ∃ a : AtomicEvent, ∃ q : Pattern, p = ofAtom a * q := by sorry

lemma exists_irreducible_factor {p : Pattern} (h : p ≠ 1) :
  ∃ q : Pattern, IsIrreducible q ∧ ∃ r : Pattern, p = q * r := by sorry

lemma pattern_eq_prod_atoms (p : Pattern) :
  ∃ atoms : List AtomicEvent, p = atoms.map ofAtom |>.prod := by sorry

-- Grade and irreducibility

lemma grade_irreducible_eq_atomicCost {p : Pattern}
  (h : IsIrreducible p) : ∃ a : AtomicEvent,
    p = ofAtom a ∧ grade p = atomicCost a := by sorry

lemma min_grade_irreducible :
  ∃ p : Pattern, IsIrreducible p ∧
    ∀ q : Pattern, IsIrreducible q → grade p ≤ grade q := by sorry

-- Pattern counting

lemma finite_patterns_length_n (n : ℕ) :
  {p : Pattern | length p = n}.Finite := by sorry

lemma finite_patterns_grade_le_n (n : ℝ≥0) :
  {p : Pattern | grade p ≤ n}.Finite := by sorry

lemma finite_irreducibles_grade_le_n (n : ℝ≥0) :
  {p : Pattern | IsIrreducible p ∧ grade p ≤ n}.Finite := by sorry

-- Pattern ordering

lemma exists_pattern_grade_eq (n : ℝ≥0) :
  ∃ p : Pattern, grade p = n := by sorry

lemma exists_irreducible_grade_between {a b : ℝ≥0} (h : a < b) :
  ∃ p : Pattern, IsIrreducible p ∧ a < grade p ∧ grade p < b := by sorry

end RecognitionScience.Pattern.Lemmas
