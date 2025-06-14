/-
  EIGHT-BEAT OPERATOR LEMMAS

  Small computational lemmas for the eight-beat tick operator.
-/

import RecognitionScience.Pattern.EightBeat
import RecognitionScience.Pattern.Lemmas.BasicInequalities

namespace RecognitionScience.Pattern.Lemmas

open Pattern EightBeat

-- Basic modular arithmetic

lemma add_one_mod_eight (n : ℕ) : (n + 1) % 8 = if n % 8 = 7 then 0 else n % 8 + 1 := by sorry

lemma add_eight_mod_eight (n : ℕ) : (n + 8) % 8 = n % 8 := by sorry

lemma mul_eight_mod_eight (n k : ℕ) : (n + 8 * k) % 8 = n % 8 := by sorry

lemma mod_eight_lt (n : ℕ) : n % 8 < 8 := by sorry

lemma mod_eight_le_seven (n : ℕ) : n % 8 ≤ 7 := by sorry

-- Tick atomic properties

lemma tick_atomic_add_eight (a : AtomicEvent) :
  tick_atomic (a + 8) = tick_atomic a := by sorry

lemma tick_atomic_iterate_one (a : AtomicEvent) :
  tick_atomic a = (a + 1) % 8 := by sorry

lemma tick_atomic_iterate_n (a : AtomicEvent) (n : ℕ) :
  (tick_atomic^[n]) a = (a + n) % 8 := by sorry

lemma tick_atomic_iterate_eight (a : AtomicEvent) :
  (tick_atomic^[8]) a = a := by sorry

lemma tick_atomic_injective : Function.Injective tick_atomic := by sorry

lemma tick_atomic_surjective : Function.Surjective tick_atomic := by sorry

-- Tick pattern properties

lemma tick_preserves_length (p : Pattern) : length (tick p) = length p := by sorry

lemma tick_preserves_ne_one {p : Pattern} (h : p ≠ 1) : tick p ≠ 1 := by sorry

lemma tick_injective : Function.Injective tick := by sorry

lemma tick_surjective : Function.Surjective tick := by sorry

lemma tick_bijective : Function.Bijective tick := by sorry

-- Eight-fold iteration

lemma tick_iterate_one : tick^[1] = tick := by sorry

lemma tick_iterate_two (p : Pattern) : (tick^[2]) p = tick (tick p) := by sorry

lemma tick_iterate_four_ne_id : ∃ p : Pattern, (tick^[4]) p ≠ p := by sorry

lemma tick_iterate_eight_eq_id : tick^[8] = id := by sorry

lemma tick_iterate_mod_eight (n : ℕ) : tick^[n] = tick^[n % 8] := by sorry

-- ZMod 8 properties

lemma eight_beat_order : orderOf (1 : ZMod 8) = 8 := by sorry

lemma eight_beat_add (a b : ZMod 8) : (a + b).val = (a.val + b.val) % 8 := by sorry

lemma eight_beat_neg (a : ZMod 8) : (-a).val = if a.val = 0 then 0 else 8 - a.val := by sorry

lemma eight_beat_sub (a b : ZMod 8) : (a - b).val = (a.val + (8 - b.val)) % 8 := by sorry

-- Tick action properties

lemma tick_action_zero (p : Pattern) : tick_action 0 p = p := by sorry

lemma tick_action_one (p : Pattern) : tick_action 1 p = tick p := by sorry

lemma tick_action_add (m n : EightBeat) (p : Pattern) :
  tick_action (m + n) p = tick_action m (tick_action n p) := by sorry

lemma tick_action_eight (p : Pattern) : tick_action 0 p = p := by sorry

-- Invariance properties

lemma tick_invariant_one : tick_invariant 1 := by sorry

lemma not_tick_invariant_ofAtom (a : AtomicEvent) : ¬tick_invariant (ofAtom a) := by sorry

lemma tick_invariant_iff_eq_one (p : Pattern) : tick_invariant p ↔ p = 1 := by sorry

-- Commutation relations

lemma tick_commutes_grade (p : Pattern) : grade (tick p) = grade p := by sorry

lemma tick_commutes_gradeNat (p : Pattern) : gradeNat (tick p) = gradeNat p := by sorry

lemma tick_preserves_irreducible (p : Pattern) :
  IsIrreducible p ↔ IsIrreducible (tick p) := by sorry

-- Eigenvalue properties

lemma eight_roots_of_unity :
  ∀ k : Fin 8, (exp (2 * π * I * k / 8))^8 = 1 := by sorry

lemma distinct_eight_roots :
  ∀ j k : Fin 8, j ≠ k → exp (2 * π * I * j / 8) ≠ exp (2 * π * I * k / 8) := by sorry

lemma tick_eigenvalues_card : tick_eigenvalues.card = 8 := by
rw [tick_eigenvalues]
simp [Finset.card_insert_of_not_mem]
repeat {
  apply Finset.card_insert_of_not_mem
  simp [mem_insert]
  intro h
  cases h
  all_goals {
    try { contradiction }
    try {
      simp at h
      cases h
      all_goals { contradiction }
    }
  }
}
simp
norm_num

end RecognitionScience.Pattern.Lemmas
