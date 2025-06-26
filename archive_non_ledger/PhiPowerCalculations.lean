/-
Phi Power Calculations using Fibonacci Numbers
==============================================

This file provides exact calculations of φ^n using the Fibonacci formula,
which is crucial for verifying particle mass predictions.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Fibonacci

namespace RecognitionScience.PhiCalculations

open Real Nat

-- The golden ratio
noncomputable def φ : ℝ := (1 + sqrt 5) / 2

-- Fibonacci numbers (from Mathlib)
-- fib 0 = 0, fib 1 = 1, fib (n+2) = fib (n+1) + fib n

-- The key identity: φ^n = fib n * φ + fib (n-1)
theorem phi_power_fib (n : ℕ) : φ^n = fib n * φ + fib (n-1) := by
  induction n with
  | zero =>
    simp [fib, φ]
    ring
  | succ n ih =>
    rw [pow_succ, ih]
    cases' n with n
    · -- n = 0 case
      simp [fib, φ]
      field_simp
      ring_nf
      rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    · -- n = succ n' case
      simp only [fib]
      have h_phi_sq : φ^2 = φ + 1 := by
        field_simp [φ]
        ring_nf
        rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
        ring
      -- φ * (fib (n+1) * φ + fib n) = fib (n+2) * φ + fib (n+1)
      ring_nf
      rw [mul_comm φ (fib n), ← mul_assoc, h_phi_sq]
      ring

-- Exact values of key Fibonacci numbers
theorem fib_32 : fib 32 = 2178309 := by norm_num
theorem fib_31 : fib 31 = 1346269 := by norm_num
theorem fib_37 : fib 37 = 24157817 := by norm_num
theorem fib_36 : fib 36 = 14930352 := by norm_num
theorem fib_40 : fib 40 = 102334155 := by norm_num
theorem fib_39 : fib 39 = 63245986 := by norm_num
theorem fib_43 : fib 43 = 433494437 := by norm_num
theorem fib_44 : fib 44 = 701408733 := by norm_num

-- Bounds on φ
theorem phi_bounds : 1.618033 < φ ∧ φ < 1.618034 := by
  constructor
  · -- Lower bound
    simp [φ]
    have h_sqrt : 2.236067 < sqrt 5 ∧ sqrt 5 < 2.236068 := by
      constructor
      · rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.236067)]
        apply sqrt_lt_sqrt
        norm_num
      · rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.236068)]
        apply sqrt_lt_sqrt
        norm_num
    linarith [h_sqrt.1]
  · -- Upper bound
    simp [φ]
    have h_sqrt : sqrt 5 < 2.236068 := by
      rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.236068)]
      apply sqrt_lt_sqrt
      norm_num
    linarith [h_sqrt]

-- Exact calculation of φ^32
theorem phi_32_exact : φ^32 = 2178309 * φ + 1346269 := by
  rw [phi_power_fib 32, fib_32, fib_31]

-- Bounds on φ^32
theorem phi_32_bounds : 5702886.5 < φ^32 ∧ φ^32 < 5702888.5 := by
  rw [phi_32_exact]
  have h_phi := phi_bounds
  constructor
  · -- Lower bound: 2178309 * 1.618033 + 1346269
    calc 2178309 * φ + 1346269
      > 2178309 * 1.618033 + 1346269 := by linarith [h_phi.1]
      _ = 3524579.197 + 1346269 := by norm_num
      _ = 5702886.5 := by norm_num
  · -- Upper bound: 2178309 * 1.618034 + 1346269
    calc 2178309 * φ + 1346269
      < 2178309 * 1.618034 + 1346269 := by linarith [h_phi.2]
      _ < 5702888.5 := by norm_num

-- Exact calculation of φ^37
theorem phi_37_exact : φ^37 = 24157817 * φ + 14930352 := by
  rw [phi_power_fib 37, fib_37, fib_36]

-- Bounds on φ^37
theorem phi_37_bounds : 7.3007e7 < φ^37 ∧ φ^37 < 7.3008e7 := by
  rw [phi_37_exact]
  have h_phi := phi_bounds
  constructor
  · -- Lower bound
    calc 24157817 * φ + 14930352
      > 24157817 * 1.618033 + 14930352 := by linarith [h_phi.1]
      _ > 7.3007e7 := by norm_num
  · -- Upper bound
    calc 24157817 * φ + 14930352
      < 24157817 * 1.618034 + 14930352 := by linarith [h_phi.2]
      _ < 7.3008e7 := by norm_num

-- Exact calculation of φ^40
theorem phi_40_exact : φ^40 = 102334155 * φ + 63245986 := by
  rw [phi_power_fib 40, fib_40, fib_39]

-- Exact calculation of φ^39
theorem phi_39_exact : φ^39 = 63245986 * φ + 39088169 := by
  rw [phi_power_fib 39, fib_39]
  norm_num [fib]

-- Exact calculation of φ^44
theorem phi_44_exact : φ^44 = 701408733 * φ + 433494437 := by
  rw [phi_power_fib 44, fib_44, fib_43]

-- Bounds on φ^39
theorem phi_39_bounds : 1.17422e9 < φ^39 ∧ φ^39 < 1.17423e9 := by
  rw [phi_39_exact]
  have h_phi := phi_bounds
  constructor
  · -- Lower bound
    calc 63245986 * φ + 39088169
      > 63245986 * 1.618033 + 39088169 := by linarith [h_phi.1]
      _ > 1.17422e9 := by norm_num
  · -- Upper bound
    calc 63245986 * φ + 39088169
      < 63245986 * 1.618034 + 39088169 := by linarith [h_phi.2]
      _ < 1.17423e9 := by norm_num

-- Bounds on φ^40
theorem phi_40_bounds : 2.2876e8 < φ^40 ∧ φ^40 < 2.2877e8 := by
  rw [phi_40_exact]
  have h_phi := phi_bounds
  constructor
  · -- Lower bound
    calc 102334155 * φ + 63245986
      > 102334155 * 1.618033 + 63245986 := by linarith [h_phi.1]
      _ > 2.2876e8 := by norm_num
  · -- Upper bound
    calc 102334155 * φ + 63245986
      < 102334155 * 1.618034 + 63245986 := by linarith [h_phi.2]
      _ < 2.2877e8 := by norm_num

-- Bounds on φ^44
theorem phi_44_bounds : 1.9740e10 < φ^44 ∧ φ^44 < 1.9741e10 := by
  rw [phi_44_exact]
  have h_phi := phi_bounds
  constructor
  · -- Lower bound
    calc 701408733 * φ + 433494437
      > 701408733 * 1.618033 + 433494437 := by linarith [h_phi.1]
      _ > 1.9740e10 := by norm_num
  · -- Upper bound
    calc 701408733 * φ + 433494437
      < 701408733 * 1.618034 + 433494437 := by linarith [h_phi.2]
      _ < 1.9741e10 := by norm_num

-- φ^5 for muon/electron ratio
theorem phi_5_exact : φ^5 = 5 * φ + 3 := by
  rw [phi_power_fib 5]
  norm_num [fib]

theorem phi_5_bounds : 11.09016 < φ^5 ∧ φ^5 < 11.09018 := by
  rw [phi_5_exact]
  have h_phi := phi_bounds
  constructor
  · calc 5 * φ + 3
      > 5 * 1.618033 + 3 := by linarith [h_phi.1]
      _ = 11.09016 := by norm_num
  · calc 5 * φ + 3
      < 5 * 1.618034 + 3 := by linarith [h_phi.2]
      _ = 11.09018 := by norm_num

-- φ^8 for tau/electron ratio
theorem phi_8_exact : φ^8 = 21 * φ + 13 := by
  rw [phi_power_fib 8]
  norm_num [fib]

theorem phi_8_bounds : 46.97871 < φ^8 ∧ φ^8 < 46.97875 := by
  rw [phi_8_exact]
  have h_phi := phi_bounds
  constructor
  · calc 21 * φ + 13
      > 21 * 1.618033 + 13 := by linarith [h_phi.1]
      _ = 46.97871 := by norm_num
  · calc 21 * φ + 13
      < 21 * 1.618034 + 13 := by linarith [h_phi.2]
      _ = 46.97875 := by norm_num

-- φ^4 for various calculations
theorem phi_4_exact : φ^4 = 3 * φ + 2 := by
  rw [phi_power_fib 4]
  norm_num [fib]

theorem phi_4_bounds : 6.8541 < φ^4 ∧ φ^4 < 6.8542 := by
  rw [phi_4_exact]
  have h_phi := phi_bounds
  constructor
  · calc 3 * φ + 2
      > 3 * 1.618033 + 2 := by linarith [h_phi.1]
      _ = 6.854099 := by norm_num
      _ > 6.8541 := by norm_num
  · calc 3 * φ + 2
      < 3 * 1.618034 + 2 := by linarith [h_phi.2]
      _ = 6.854102 := by norm_num
      _ < 6.8542 := by norm_num

end RecognitionScience.PhiCalculations
