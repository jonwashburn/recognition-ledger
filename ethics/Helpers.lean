/-
Recognition Science - Ethics Helper Lemmas
==========================================

This file contains helper lemmas for proving the ethics theorems.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Recognition.Util.List

namespace RecognitionScience.Ethics

open Real

/-! ## Helper lemmas for the golden ratio -/

lemma Real.goldenRatio_pos : 0 < goldenRatio := by
  simp [goldenRatio]
  norm_num

lemma Real.one_lt_goldenRatio : 1 < goldenRatio := by
  simp [goldenRatio]
  norm_num

/-! ## Helper lemmas for lists -/

/-- Sum of a list is less than another if there exists a strict inequality and all others are ≤ -/
lemma List.sum_lt_sum_of_exists_lt_of_all_le {α : Type*} [OrderedAddCommMonoid α]
  (l₁ l₂ : List α)
  (h_len : l₁.length = l₂.length)
  (h_exists : ∃ i, i < l₁.length ∧ l₁.get ⟨i, by simp; exact i.2⟩ < l₂.get ⟨i, by simp [h_len]; exact i.2⟩)
  (h_all : ∀ i, i < l₁.length → l₁.get ⟨i, by simp; exact i.2⟩ ≤ l₂.get ⟨i, by simp [h_len]; exact i.2⟩) :
  l₁.sum < l₂.sum := by
  -- Now we simply call the shared utility lemma
  have := Recognition.Util.List.sum_lt_sum_of_exists_lt_of_all_le l₁ l₂ h_len h_exists h_all
  exact this

/-- Alternative version for mapped lists -/
lemma List.sum_lt_sum_of_exists_lt_of_all_le' {α β : Type*} [OrderedAddCommMonoid β]
  (l : List α) (f g : α → β)
  (h_exists : ∃ x ∈ l, f x < g x)
  (h_all : ∀ x ∈ l, f x ≤ g x) :
  (l.map f).sum < (l.map g).sum := by
  exact Recognition.Util.List.sum_lt_sum_of_exists_lt_of_all_le' l f g h_exists h_all

/-! ## Helper lemmas for Int operations -/

/-- Converting Int.natAbs inequalities -/
lemma Int.lt_of_natAbs_lt_natAbs {a b : Int} : Int.natAbs a < Int.natAbs b → a < b ∨ b < a := by
  intro h
  cases a <;> cases b <;> simp [Int.natAbs] at h ⊢
  · omega
  · right; omega
  · left; omega
  · omega

/-! ## Helper lemmas for floor operations -/

/-- Floor of division by golden ratio reduces absolute value -/
lemma floor_div_goldenRatio_reduces_abs (x : Int) :
  Int.natAbs (Int.floor (x / goldenRatio)) ≤ Int.natAbs x := by
  cases x with
  | ofNat n =>
    simp [Int.natAbs]
    have : Int.floor (↑n / goldenRatio) ≤ n := by
      apply Int.floor_le
      simp
      exact div_le_self (Nat.cast_nonneg n) (le_of_lt one_lt_goldenRatio)
    have : 0 ≤ Int.floor (↑n / goldenRatio) := by
      apply Int.floor_nonneg
      exact div_nonneg (Nat.cast_nonneg n) (le_of_lt goldenRatio_pos)
    omega
  | negSucc n =>
    simp [Int.natAbs]
    have : Int.floor (Int.negSucc n / goldenRatio) ≥ Int.negSucc n := by
      apply Int.le_floor
      simp
      have : Int.negSucc n < 0 := by simp
      exact div_le_self_of_neg this (le_of_lt one_lt_goldenRatio)
    omega

/-! ## Helper lemmas for exponential bounds -/

/-- Exponential decay bound -/
lemma exp_decay_bound {ε Γ : Real} (h_eps : 0 < ε) (h_Γ : 0 < Γ) :
  ∃ T : Real, ∀ t > T, exp (-Γ * t) < ε := by
  use -log ε / Γ
  intro t h_t
  rw [exp_lt_iff_lt_log h_eps]
  calc -Γ * t < -Γ * (-log ε / Γ) := by
    apply mul_lt_mul_of_neg_left h_t
    linarith
  _ = log ε := by
    field_simp
    ring

-- Additional lemmas for exponential decay
section ExponentialDecay

/-- Simplified exponential decay bound -/
lemma simple_exp_decay (n : Nat) (base : Real) (h_base : 0 < base ∧ base < 1) :
  base ^ n ≤ base ^ 1 := by
  cases n with
  | zero => simp; exact h_base.1.le
  | succ n =>
    apply pow_le_pow_of_le_one
    · exact h_base.1.le
    · exact h_base.2.le
    · simp

/-- Powers of 1/φ decrease -/
lemma inv_phi_pow_decreasing (n : Nat) :
  (1 / Real.goldenRatio) ^ (n + 1) < (1 / Real.goldenRatio) ^ n := by
  apply pow_lt_pow_of_lt_left
  · apply div_pos; norm_num; exact Real.goldenRatio_pos
  · apply div_lt_one Real.goldenRatio_pos
    exact Real.one_lt_goldenRatio
  · simp

end ExponentialDecay

end RecognitionScience.Ethics
