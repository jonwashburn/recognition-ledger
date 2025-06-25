import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

namespace RecognitionScience.Basic

-- The simplest involution with exactly 2 fixed points:
-- Swap x with 2-x, except at fixed points 0 and 2
noncomputable def simple_involution : ℝ → ℝ :=
  fun x => if x = 0 ∨ x = 2 then x else 2 - x

theorem simple_involution_involutive : Function.Involutive simple_involution := by
  intro x
  unfold simple_involution
  by_cases h : x = 0 ∨ x = 2
  · simp [h]
  · simp [h]
    push_neg at h
    have : ¬(2 - x = 0 ∨ 2 - x = 2) := by
      push_neg
      constructor
      · linarith [h.1]
      · linarith [h.2]
    simp [this]
    ring

theorem simple_involution_fixed_points :
  {x : ℝ | simple_involution x = x} = {0, 2} := by
  ext x
  simp [Set.mem_setOf, simple_involution]
  constructor
  · intro h
    by_cases hx : x = 0 ∨ x = 2
    · exact hx
    · simp [hx] at h
      have : x = 1 := by linarith
      -- But 1 is not 0 or 2, contradiction
      exfalso
      apply hx
      right
      linarith
  · intro h
    cases h with
    | inl h0 => simp [h0]
    | inr h2 => simp [h2]

-- General construction for any two distinct points
noncomputable def two_point_involution (a b : ℝ) (h : a ≠ b) : ℝ → ℝ :=
  fun x => if x = a ∨ x = b then x else a + b - x

theorem two_point_involution_involutive (a b : ℝ) (h : a ≠ b) :
  Function.Involutive (two_point_involution a b h) := by
  intro x
  unfold two_point_involution
  by_cases hx : x = a ∨ x = b
  · simp [hx]
  · simp [hx]
    push_neg at hx
    have : ¬(a + b - x = a ∨ a + b - x = b) := by
      push_neg
      constructor
      · intro h_eq
        have : x = b := by linarith
        exact hx.2 this
      · intro h_eq
        have : x = a := by linarith
        exact hx.1 this
    simp [this]
    ring

theorem two_point_involution_exactly_two_fixed (a b : ℝ) (h : a ≠ b) :
  ∃! (s : Finset ℝ), s.card = 2 ∧ (∀ x : ℝ, x ∈ s ↔ two_point_involution a b h x = x) := by
  use {a, b}
  simp [Finset.card_insert_of_not_mem h, Finset.card_singleton]
  constructor
  · constructor
    · rfl
    · intro x
      simp [two_point_involution]
      constructor
      · intro hx
        cases hx with
        | inl ha => simp [ha]
        | inr hb => simp [hb]
      · intro h
        by_cases hx : x = a ∨ x = b
        · exact hx
        · simp [hx] at h
          have : x = (a + b) / 2 := by linarith
          -- The midpoint is only fixed if a = b, contradiction
          exfalso
          have : a = b := by linarith
          exact h this
  · intro s ⟨hcard, hiff⟩
    -- s has exactly the fixed points, which are a and b
    ext x
    simp
    rw [← hiff]
    rfl

end RecognitionScience.Basic
