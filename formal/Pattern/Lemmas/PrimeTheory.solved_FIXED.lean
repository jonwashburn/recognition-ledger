/-
  PRIME NUMBER THEORY LEMMAS

  Small lemmas about primes that automated solvers can handle.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.Divisors
import RecognitionScience.Pattern.Lemmas.BasicInequalities

namespace RecognitionScience.Pattern.Lemmas

open Nat

-- Basic prime properties

lemma prime_two : Prime 2 := by sorry

lemma prime_three : Prime 3 := by sorry

lemma prime_five : Prime 5 := by sorry

lemma not_prime_zero : ¬Prime 0 := by sorry

lemma not_prime_one : ¬Prime 1 := by sorry

lemma not_prime_four : ¬Prime 4 := by sorry

lemma prime_odd_or_two {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p := by sorry

lemma prime_pos {p : ℕ} (hp : Prime p) : 0 < p := by sorry

lemma prime_ne_zero {p : ℕ} (hp : Prime p) : p ≠ 0 := by sorry

lemma prime_ne_one {p : ℕ} (hp : Prime p) : p ≠ 1 := by sorry

-- Divisibility

lemma prime_dvd_mul {p a b : ℕ} (hp : Prime p) :
  p ∣ a * b ↔ p ∣ a ∨ p ∣ b := by sorry

lemma prime_dvd_pow {p a : ℕ} (hp : Prime p) (n : ℕ) :
  p ∣ a^n ↔ p ∣ a ∧ n ≠ 0 := by sorry

lemma not_prime_mul {a b : ℕ} (ha : 1 < a) (hb : 1 < b) :
  ¬Prime (a * b) := by sorry

-- Prime counting

lemma nth_prime_zero : nth_prime 0 = 2 := by sorry

lemma nth_prime_one : nth_prime 1 = 3 := by sorry

lemma nth_prime_two : nth_prime 2 = 5 := by sorry

lemma nth_prime_lt_nth_prime {m n : ℕ} (h : m < n) :
  nth_prime m < nth_prime n := by sorry

lemma nth_prime_le_nth_prime {m n : ℕ} (h : m ≤ n) :
  nth_prime m ≤ nth_prime n := by sorry

lemma nth_prime_injective : Function.Injective nth_prime := by sorry

lemma exists_nth_prime_eq {p : ℕ} (hp : Prime p) :
  ∃ n, nth_prime n = p := by sorry

-- Prime bounds

lemma nth_prime_pos (n : ℕ) : 0 < nth_prime n := by sorry

lemma two_le_nth_prime (n : ℕ) : 2 ≤ nth_prime n := by sorry

lemma nth_prime_ge_n_plus_two (n : ℕ) : n + 2 ≤ nth_prime n := by sorry

lemma nth_prime_le_two_pow (n : ℕ) : nth_prime n ≤ 2^(n + 2) := by sorry

-- Factorization

lemma prod_factors {n : ℕ} (hn : 1 < n) : n.factors.prod = n := by sorry

lemma mem_factors_iff_prime {n p : ℕ} (hn : n ≠ 0) :
  p ∈ n.factors ↔ Prime p ∧ p ∣ n := by sorry

lemma factors_unique {n : ℕ} (l : List ℕ)
  (hl : ∀ p ∈ l, Prime p) (hp : l.prod = n) :
  l.toMultiset = n.factors.toMultiset := by sorry

-- Coprimality

lemma coprime_one_left (n : ℕ) : Coprime 1 n := by sorry

lemma coprime_one_right (n : ℕ) : Coprime n 1 := by sorry

lemma coprime_comm {a b : ℕ} : Coprime a b ↔ Coprime b a := by sorry

lemma coprime_mul_left {a b c : ℕ} :
  Coprime (a * b) c ↔ Coprime a c ∧ Coprime b c := by sorry

lemma coprime_pow_left {a b : ℕ} (n : ℕ) :
  Coprime (a^n) b ↔ Coprime a b ∨ n = 0 := by sorry

-- Prime gaps

lemma exists_prime_between {n : ℕ} (hn : 2 ≤ n) :
  ∃ p, Prime p ∧ n < p ∧ p < 2 * n := by sorry

lemma infinite_primes : ∀ n, ∃ p, Prime p ∧ n < p := by
  intro n
  let m := (range n).prod + 1
  have h1 : 0 < m := by
    apply Nat.succ_pos
  have h2 : ∀ k, k ∈ range n → k ∣ m - 1 := by
    intro k hk
    apply Nat.dvd_sub' (Nat.dvd_prod_of_mem_range hk) 
    exact Nat.dvd_one
  obtain ⟨p, hp⟩ := Nat.min_fac_prime h1
  have h3 : p ∣ m := by exact hp.1
  have h4 : n < p := by
    by_contra h
    push_neg at h
    have : p ∣ m - 1 := h2 p (Nat.mem_range.2 h)
    have : p ∣ 1 := Nat.dvd_sub h3 this
    exact hp.2.not_dvd_one this
  exact ⟨p, ⟨hp.2, h4⟩⟩

-- Modular arithmetic with primes

lemma fermat_little {p : ℕ} (hp : Prime p) {a : ℕ} (ha : ¬p ∣ a) :
  a^(p - 1) ≡ 1 [MOD p] := by sorry

lemma wilson_theorem {p : ℕ} (hp : Prime p) :
  (p - 1).factorial ≡ p - 1 [MOD p] := by sorry

end RecognitionScience.Pattern.Lemmas
