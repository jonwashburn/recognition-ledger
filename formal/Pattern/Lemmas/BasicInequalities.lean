/-
  BASIC INEQUALITY LEMMAS

  Small lemmas about inequalities that automated solvers can handle.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace RecognitionScience.Pattern.Lemmas

open Real Complex

-- Basic real inequalities

lemma one_lt_two : (1 : ℝ) < 2 := by sorry

lemma half_between_zero_one : 0 < (1/2 : ℝ) ∧ (1/2 : ℝ) < 1 := by sorry

lemma half_plus_half : (1/2 : ℝ) + (1/2 : ℝ) = 1 := by sorry

lemma pos_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by sorry

lemma sq_nonneg (x : ℝ) : 0 ≤ x^2 := by sorry

lemma sq_pos_of_ne_zero {x : ℝ} (h : x ≠ 0) : 0 < x^2 := by sorry

-- Complex inequalities

lemma abs_exp_eq_exp_re (z : ℂ) : Complex.abs (exp z) = Real.exp z.re := by sorry

lemma abs_mul (z w : ℂ) : Complex.abs (z * w) = Complex.abs z * Complex.abs w := by sorry

lemma abs_pow (z : ℂ) (n : ℕ) : Complex.abs (z^n) = (Complex.abs z)^n := by sorry

lemma abs_inv_eq_inv_abs {z : ℂ} (hz : z ≠ 0) : Complex.abs z⁻¹ = (Complex.abs z)⁻¹ := by sorry

-- Exponential inequalities

lemma exp_pos (x : ℝ) : 0 < Real.exp x := by sorry

lemma exp_ne_zero (x : ℝ) : Real.exp x ≠ 0 := by sorry

lemma exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by sorry

lemma exp_mul (x : ℝ) (n : ℕ) : Real.exp (n * x) = (Real.exp x)^n := by sorry

-- Complex exponential

lemma cexp_ne_zero (z : ℂ) : exp z ≠ 0 := by sorry

lemma cexp_add (z w : ℂ) : exp (z + w) = exp z * exp w := by sorry

lemma cexp_mul_I_pi : exp (I * π) = -1 := by sorry

lemma cexp_two_pi_I : exp (2 * π * I) = 1 := by sorry

-- Logarithm inequalities

lemma log_one : Real.log 1 = 0 := by sorry

lemma log_pos_of_gt_one {x : ℝ} (h : 1 < x) : 0 < Real.log x := by sorry

lemma log_neg_of_lt_one {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) : Real.log x < 0 := by sorry

lemma log_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  Real.log (x * y) = Real.log x + Real.log y := by sorry

-- Prime bounds

lemma two_is_prime : Nat.Prime 2 := by sorry

lemma prime_gt_one {p : ℕ} (hp : Nat.Prime p) : 1 < p := by sorry

lemma prime_ge_two {p : ℕ} (hp : Nat.Prime p) : 2 ≤ p := by sorry

lemma nth_prime_ge (n : ℕ) : n + 2 ≤ Nat.nth_prime n := by sorry

-- Summability helpers

lemma sum_pos_of_pos {α : Type*} {f : α → ℝ} {s : Finset α}
  (h : ∀ x ∈ s, 0 < f x) : 0 < s.sum f := by sorry

lemma tsum_pos_of_pos {α : Type*} {f : α → ℝ}
  (h : ∀ x, 0 < f x) (hs : Summable f) : 0 < ∑' x, f x := by sorry

-- Modular arithmetic

lemma mod_add_mod (a b n : ℕ) : (a + b) % n = ((a % n) + (b % n)) % n := by sorry

lemma mod_mul_mod (a b n : ℕ) : (a * b) % n = ((a % n) * (b % n)) % n := by sorry

lemma mod_mod (a n : ℕ) : (a % n) % n = a % n := by sorry

lemma mod_lt {a n : ℕ} (h : 0 < n) : a % n < n := by sorry

-- Set membership

lemma mem_interval {x a b : ℝ} : x ∈ Set.Ioo a b ↔ a < x ∧ x < b := by sorry

lemma mem_critical_strip {s : ℂ} :
  s ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} ↔ 0 < s.re ∧ s.re < 1 := by sorry

lemma mem_critical_line {s : ℂ} :
  s ∈ {z : ℂ | z.re = 1/2} ↔ s.re = 1/2 := by sorry

end RecognitionScience.Pattern.Lemmas
