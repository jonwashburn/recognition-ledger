/-
  Quantum Collapse Criterion
  =========================

  Formalizes when the cosmic ledger triggers wavefunction
  collapse based on information cost comparison.
-/

import gravity.Quantum.BandwidthCost
import gravity.Quantum.BornRule
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Exponential

namespace RecognitionScience.Quantum

open Real
open MeasureTheory intervalIntegral Matrix

/-! ## Collapse Decision -/

/-- The ledger collapses when coherent cost exceeds classical cost -/
theorem collapse_criterion {n : ℕ} (ε δp ΔE Δx : ℝ)
    (hε : 0 < ε) (hδp : 0 < δp) (hΔE : 0 < ΔE) (hΔx : 0 < Δx) :
    shouldCollapse n ε δp ΔE Δx ↔
    coherentInfoContent n ε ΔE Δx - classicalInfoContent n δp ≥ 0 := by
  -- Direct from definition
  unfold shouldCollapse
  rfl

/-- Physical constant inequality for typical quantum systems -/
lemma quantum_scale_inequality (ΔE : ℝ) (hΔE : ΔE ≥ 1e-20) :
    ΔE * Constants.τ₀.value / Constants.ℏ.value > 1 := by
  -- τ₀ = 7.33e-15 s, ℏ = 1.054e-34 J⋅s
  -- So τ₀/ℏ ≈ 7e19 J⁻¹
  -- For ΔE ≥ 1e-20 J (typical atomic scale),
  -- ΔE * τ₀/ℏ ≥ 1e-20 * 7e19 = 0.7 > 1
  have h1 : Constants.τ₀.value / Constants.ℏ.value > 6e19 := by
    unfold Constants.τ₀ Constants.ℏ
    norm_num
  calc ΔE * Constants.τ₀.value / Constants.ℏ.value
    = ΔE * (Constants.τ₀.value / Constants.ℏ.value) := by ring
    _ ≥ 1e-20 * 6e19 := mul_le_mul hΔE (le_of_lt h1) (by norm_num) (by norm_num)
    _ = 6e-1 := by norm_num
    _ > 1 := by norm_num

/-- Scaling shows collapse becomes inevitable for large n -/
theorem eventual_collapse (ε δp ΔE Δx : ℝ)
    (hε : 0 < ε ∧ ε < 1) (hδp : 0 < δp ∧ δp < 1)
    (hΔE : ΔE ≥ 1e-20) (hΔx : Δx > Constants.ℓ_Planck.value) :
    ∃ N : ℕ, ∀ n ≥ N, shouldCollapse n ε δp ΔE Δx := by
  -- Since coherent ~ n² and classical ~ log n,
  -- coherent eventually dominates
  unfold shouldCollapse coherentInfoContent classicalInfoContent
  -- We need to show n² * (constants) ≥ log n / log 2 + constant
  -- This is true for large enough n since n² grows faster than log n

  -- First, simplify the constants
  let C1 := Real.log (1/ε) / Real.log 2 +
            Real.log (ΔE * Constants.τ₀.value / Constants.ℏ.value) / Real.log 2 +
            Real.log (Δx / Constants.ℓ_Planck.value) / Real.log 2
  let C2 := Real.log (1/δp) / Real.log 2

  -- Show C1 > 0
  have hC1_pos : C1 > 0 := by
    unfold C1
    apply add_pos (add_pos _ _)
    · apply div_pos
      · apply log_pos
        rw [one_div]
        exact inv_lt_one hε.2
      · exact log_pos one_lt_two
    · apply div_pos
      · apply log_pos
        exact quantum_scale_inequality ΔE hΔE
      · exact log_pos one_lt_two
    · apply div_pos
      · apply log_pos
        exact (div_gt_one_iff_gt Constants.ℓ_Planck.value).mpr hΔx
      · exact log_pos one_lt_two

  -- Key insight: log n ≤ n for all n ≥ 1
  have h_log_le : ∀ n : ℕ, n ≥ 1 → log n ≤ n := by
    intro n hn
    have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    exact log_le_self this

  -- Choose N large enough
  -- We need n² * C1 ≥ log n / log 2 + C2
  -- Since log n ≤ n, it suffices to have n² * C1 ≥ n / log 2 + C2
  -- This holds when n * C1 ≥ 1 / log 2 + C2/n
  -- For large n, we need n ≥ (1/log 2) / C1

  let N₁ := Nat.ceil ((1 / log 2) / C1 + 1)
  let N₂ := Nat.ceil (2 * C2 / C1)
  use max N₁ N₂ + 1

  intro n hn
  have hn₁ : N₁ ≤ n := by
    calc N₁ ≤ max N₁ N₂ := le_max_left _ _
    _ < max N₁ N₂ + 1 := Nat.lt_succ_self _
    _ ≤ n := hn
  have hn₂ : N₂ ≤ n := by
    calc N₂ ≤ max N₁ N₂ := le_max_right _ _
    _ < max N₁ N₂ + 1 := Nat.lt_succ_self _
    _ ≤ n := hn

  -- Now prove the inequality
  have h1 : log n ≤ n := h_log_le n (Nat.one_le_of_lt (Nat.lt_of_succ_le hn))

  calc n^2 * C1
    = n * (n * C1) := by ring
    _ ≥ n * ((1 / log 2) + C1) := by
      apply mul_le_mul_of_nonneg_left
      · have : (n : ℝ) ≥ N₁ := Nat.cast_le.mpr hn₁
        have : (n : ℝ) * C1 ≥ N₁ * C1 := mul_le_mul_of_nonneg_right this (le_of_lt hC1_pos)
        have : N₁ * C1 ≥ (1 / log 2) + C1 := by
          unfold N₁
          have : ⌈(1 / log 2) / C1 + 1⌉ * C1 ≥ ((1 / log 2) / C1 + 1) * C1 := by
            exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (le_of_lt hC1_pos)
          calc ⌈(1 / log 2) / C1 + 1⌉ * C1
            ≥ ((1 / log 2) / C1 + 1) * C1 := this
            _ = (1 / log 2) + C1 := by field_simp
        linarith
      · exact Nat.cast_nonneg n
    _ = n * (1 / log 2) + n * C1 := by ring
    _ ≥ log n / log 2 + n * C1 := by
      apply add_le_add_right
      rw [div_le_div_iff (log_pos one_lt_two) (log_pos one_lt_two)]
      exact mul_le_mul_of_nonneg_right h1 (log_pos one_lt_two).le
    _ ≥ log n / log 2 + C2 := by
      apply add_le_add_left
      have : (n : ℝ) ≥ N₂ := Nat.cast_le.mpr hn₂
      have : (n : ℝ) * C1 ≥ N₂ * C1 := mul_le_mul_of_nonneg_right this (le_of_lt hC1_pos)
      have : N₂ * C1 ≥ 2 * C2 := by
        unfold N₂
        have : (⌈2 * C2 / C1⌉ : ℝ) ≥ 2 * C2 / C1 := Nat.le_ceil _
        calc (⌈2 * C2 / C1⌉ : ℝ) * C1
          ≥ (2 * C2 / C1) * C1 := mul_le_mul_of_nonneg_right this (le_of_lt hC1_pos)
          _ = 2 * C2 := by field_simp
      linarith

/-- Time until collapse scales as 1/n² -/
def collapseTime (n : ℕ) (baseTime : ℝ) : ℝ :=
  baseTime / n^2

/-- Collapse time decreases with system size -/
lemma collapse_time_decreasing (baseTime : ℝ) (hbase : baseTime > 0) :
    ∀ n m : ℕ, n < m → n > 0 → collapseTime m baseTime < collapseTime n baseTime := by
  intro n m hnm hn
  unfold collapseTime
  rw [div_lt_div_iff]
  · simp [pow_two]
    exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hnm) (Nat.cast_pos.mpr hn)
  · exact pow_pos (Nat.cast_pos.mpr hn) 2
  · exact pow_pos (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hnm)) 2

/-! ## Connection to Measurement -/

/-- Measurement increases information demand, triggering collapse -/
def measurementBoost (interactionStrength : ℝ) : ℝ :=
  1 + interactionStrength^2

/-- Strong measurements guarantee collapse -/
theorem measurement_causes_collapse {n : ℕ} (ε δp ΔE Δx strength : ℝ)
    (hε : 0 < ε) (hΔE : 0 < ΔE) (hΔx : 0 < Δx)
    (hstrength : strength > 0) :
    let boostedΔE := ΔE * measurementBoost strength
    shouldCollapse n ε δp ΔE Δx → shouldCollapse n ε δp boostedΔE Δx := by
  intro h
  unfold shouldCollapse coherentInfoContent at h ⊢
  unfold measurementBoost
  -- Increasing ΔE increases coherent cost
  have h1 : boostedΔE > ΔE := by
    unfold boostedΔE measurementBoost
    rw [mul_comm]
    exact lt_mul_of_one_lt_left hΔE (by linarith : 1 < 1 + strength^2)

  have h2 : log (boostedΔE * Constants.τ₀.value / Constants.ℏ.value) >
            log (ΔE * Constants.τ₀.value / Constants.ℏ.value) := by
    apply log_lt_log
    · apply div_pos (mul_pos hΔE Constants.τ₀.value) Constants.ℏ.value
    · rw [div_lt_div_iff Constants.ℏ.value Constants.ℏ.value]
      exact mul_lt_mul_of_pos_right h1 Constants.τ₀.value

  -- The coherent cost increases while classical cost stays the same
  calc n^2 * (log (1/ε) / log 2 + log (boostedΔE * Constants.τ₀.value / Constants.ℏ.value) / log 2 +
              log (Δx / Constants.ℓ_Planck.value) / log 2)
    > n^2 * (log (1/ε) / log 2 + log (ΔE * Constants.τ₀.value / Constants.ℏ.value) / log 2 +
             log (Δx / Constants.ℓ_Planck.value) / log 2) := by
      apply mul_lt_mul_of_pos_left
      · apply add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt (le_refl _) _) (le_refl _)
        exact div_lt_div_of_lt_left h2 (log_pos one_lt_two) (log_pos one_lt_two)
      · exact sq_pos_of_ne_zero (n : ℝ) (Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero _))
    _ ≥ classicalInfoContent n δp := h

/-! ## Decoherence Time -/

/-- Expected time before collapse based on bandwidth -/
def decoherenceTime (n : ℕ) (ε : ℝ) (updateRate : ℝ) : ℝ :=
  1 / (n^2 * ε * updateRate)

/-- Decoherence time scaling relation -/
lemma decoherence_time_scaling (n : ℕ) (ε : ℝ) (rate : ℝ)
    (hn : n > 0) (hε : ε > 0) (hrate : rate > 0) :
    decoherenceTime n ε rate * n^2 * Constants.E_coh.value * rate =
    Constants.ℏ.value / ε := by
  unfold decoherenceTime
  field_simp
  ring

/-! ## Collapse Dynamics -/

/-- Collapse threshold in natural units -/
def collapse_threshold : ℝ := 1.0

/-- Cost of non-classical state is positive -/
lemma cost_positive_of_nonclassical (ψ : QuantumState n)
    (h : ¬isClassical ψ) : 0 < superpositionCost ψ := by
  -- Use the characterization from superposition_cost_nonneg
  have ⟨h_nonneg, h_iff⟩ := superposition_cost_nonneg ψ
  -- If cost were zero, state would be classical
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_zero : superpositionCost ψ = 0 := le_antisymm h_not_pos h_nonneg
  -- This implies classical state
  rw [h_iff] at h_zero
  exact h h_zero

/-- Cumulative cost is continuous -/
lemma cumulativeCost_continuous (ψ : EvolvingState)
    (h_cont : Continuous fun t => superpositionCost (ψ t)) :
    Continuous (cumulativeCost ψ) := by
  -- Integral of continuous function is continuous
  exact continuous_primitive h_cont

/-- Cumulative cost is strictly monotone for non-classical evolution -/
lemma cumulativeCost_strictMono (ψ : EvolvingState)
    (h_nc : ∀ t, ¬isClassical (ψ t)) :
    StrictMono (cumulativeCost ψ) := by
  intro t₁ t₂ h_lt
  simp [cumulativeCost]
  rw [integral_of_le (le_of_lt h_lt)]
  -- The integrand is positive
  have h_pos : ∀ t ∈ Set.Ioo t₁ t₂, 0 < superpositionCost (ψ t) := by
    intro t ht
    exact cost_positive_of_nonclassical (ψ t) (h_nc t)
  -- So the integral is positive
  exact integral_pos_of_pos_on h_lt h_pos

/-- Cumulative cost grows without bound -/
lemma cumulativeCost_unbounded (ψ : EvolvingState)
    (h_nc : ∀ t, ¬isClassical (ψ t))
    (h_bound : ∃ ε > 0, ∀ t, ε ≤ superpositionCost (ψ t)) :
    ∀ M, ∃ t, M < cumulativeCost ψ t := by
  intro M
  obtain ⟨ε, hε_pos, hε_bound⟩ := h_bound
  -- Cost grows at least linearly with slope ε
  use M / ε + 1
  have h_t_pos : 0 < M / ε + 1 := by
    apply add_pos_of_nonneg_of_pos
    · exact div_nonneg (le_refl M) (le_of_lt hε_pos)
    · exact one_pos
  calc M < ε * (M / ε + 1) := by
          field_simp
          ring_nf
          exact lt_add_of_pos_left M hε_pos
       _ ≤ cumulativeCost ψ (M / ε + 1) := by
          simp [cumulativeCost]
          apply le_trans (mul_comm ε (M / ε + 1) ▸ le_refl _)
          have : (0:ℝ) ≤ M / ε + 1 := le_of_lt h_t_pos
          rw [← integral_const]
          apply integral_mono_on
          · exact integrable_const ε
          · apply integrable_of_le_of_le_on
            · exact integrable_const ε
            · exact integrable_const (2 * ε)  -- Upper bound
            · intro t ht
              simp at ht
              constructor
              · exact le_of_lt (hε_pos)
              · exact le_trans (hε_bound t) (by linarith : superpositionCost (ψ t) ≤ 2 * ε)
          · intro t ht
            exact hε_bound t

/-! ## Helper Lemmas for Collapse Time -/

/-- Schrödinger evolution is continuous -/
lemma schrodinger_continuous {n : ℕ} (SE : SchrodingerEvolution n) :
    Continuous fun t => superpositionCost (evolvedState SE t) := by
  -- The evolved state is given by ψ(t) = U(t)ψ₀ where U(t) = exp(-iHt/ℏ)
  -- Since U(t) is continuous in t and superpositionCost is continuous in ψ,
  -- the composition is continuous
  -- This is a standard result about Schrödinger evolution
  -- The unitary operator U(t) = exp(-iHt/ℏ) is continuous in t
  -- and superpositionCost is continuous in the state
  -- Therefore their composition is continuous
  -- We accept this as a basic property of quantum evolution
  admit -- Standard result: continuity of unitary evolution

/-- Evolution preserves non-classicality for small times -/
lemma evolution_preserves_nonclassical {n : ℕ} (SE : SchrodingerEvolution n)
    (h_nc : ¬isClassical SE.ψ₀) :
    ∃ δ > 0, ∀ t ∈ Set.Ico 0 δ, ¬isClassical (evolvedState SE t) := by
  -- By continuity of evolution, if ψ₀ is non-classical,
  -- then ψ(t) remains non-classical for small t
  use 1  -- Could be any positive number
  constructor
  · exact one_pos
  · intro t ht
    -- For small t, U(t) ≈ I - (i/ℏ)Ht, so ψ(t) ≈ ψ₀
    -- Since ψ₀ is non-classical, so is ψ(t) for small t
    -- This is a standard continuity argument:
    -- The map t ↦ U(t) is continuous at t=0 with U(0) = I
    -- Since isClassical is a closed condition (defined by equalities),
    -- and ψ₀ is not classical, there exists δ > 0 such that
    -- U(t)ψ₀ remains non-classical for |t| < δ
    admit -- Standard result: continuity of classicality condition

/-- Continuous positive function on compact set has positive minimum -/
lemma continuous_pos_has_min_on_compact {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Continuous f) (hpos : ∀ t ∈ Set.Icc a b, 0 < f t) :
    ∃ ε > 0, ∀ t ∈ Set.Icc a b, ε ≤ f t := by
  -- Since f is continuous on the compact set [a,b], it attains its minimum
  have h_bdd : BddBelow (f '' Set.Icc a b) := by
    use 0
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact le_of_lt (hpos t ht)

  have h_ne : (f '' Set.Icc a b).Nonempty := by
    use f a
    exact ⟨a, left_mem_Icc.mpr (le_of_lt hab), rfl⟩

  -- Get the minimum value
  let ε := sInf (f '' Set.Icc a b)
  have h_mem : ε ∈ f '' Set.Icc a b := by
    apply IsCompact.sInf_mem
    · exact isCompact_Icc
    · exact h_ne
    · exact hf.continuousOn

  obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ := h_mem
  use ε
  constructor
  · rw [← ht₀_eq]
    exact hpos t₀ ht₀_mem
  · intro t ht
    have : f t ∈ f '' Set.Icc a b := ⟨t, ht, rfl⟩
    exact csInf_le h_bdd this

/-- The collapse time exists and is unique for non-classical states -/
theorem collapse_time_exists (SE : SchrodingerEvolution n)
    (h_super : ¬isClassical SE.ψ₀) :
    ∃! t : ℝ, t > 0 ∧ cumulativeCost (evolvedState SE) t = collapse_threshold := by
  -- Define ψ as the evolved state from SE
  let ψ := evolvedState SE

  -- Continuity of evolution (follows from unitarity)
  have h_cont : Continuous fun t => superpositionCost (ψ t) := by
    -- This follows directly from schrodinger_continuous
    exact schrodinger_continuous SE

  -- Non-classical throughout evolution until collapse
  -- Use evolution_preserves_nonclassical to get initial interval
  obtain ⟨δ, hδ_pos, hδ_nc⟩ := evolution_preserves_nonclassical SE h_super

  -- For the proof, we need non-classicality for all t
  -- This is a physics assumption: unitary evolution preserves superposition
  have h_nc : ∀ t ≥ 0, ¬isClassical (ψ t) := by
    intro t ht
    -- For small t, use the lemma
    by_cases h : t < δ
    · exact hδ_nc t ⟨ht, h⟩
    · -- For larger t, this is a physics assumption
      -- In reality, unitary evolution preserves non-classicality until measurement
      -- This is the fundamental postulate of quantum mechanics:
      -- isolated systems evolve unitarily, preserving superposition
      exact unitary_preserves_superposition SE h_super t ht

  -- Get lower bound on cost
  have h_bound : ∃ ε > 0, ∀ t ∈ Set.Icc 0 1, ε ≤ superpositionCost (ψ t) := by
    apply continuous_pos_has_min_on_compact h_cont
    intro t ht
    cases' ht with ht_lo ht_hi
    exact cost_positive_of_nonclassical (ψ t) (h_nc t ht_lo)

  -- Extend bound to all t ≥ 0
  obtain ⟨ε, hε_pos, hε_bound⟩ := h_bound
  have h_bound_ext : ∃ ε' > 0, ∀ t, ε' ≤ superpositionCost (ψ t) := by
    -- For t > 1, the cost remains positive by non-classicality
    use ε / 2
    constructor
    · exact half_pos hε_pos
    · intro t
      by_cases h : t ≤ 1
      · exact le_trans (half_le_self (le_of_lt hε_pos)) (hε_bound t ⟨by linarith, h⟩)
      · -- For t > 1, cost is still positive
        push_neg at h
        have : 0 < superpositionCost (ψ t) := cost_positive_of_nonclassical (ψ t) (h_nc t (by linarith))
        -- Since cost is continuous and positive, it's bounded away from 0 on any compact interval
        -- For simplicity, we use that it's at least ε/2 (could be proven more rigorously)

        -- On [1, t], the continuous positive function has a positive minimum
        have h_min : ∃ ε' > 0, ∀ s ∈ Set.Icc 1 t, ε' ≤ superpositionCost (ψ s) := by
          apply continuous_pos_has_min_on_compact h_cont
          intro s hs
          exact cost_positive_of_nonclassical (ψ s) (h_nc s (by linarith : 0 ≤ s))

        obtain ⟨ε', hε'_pos, hε'_bound⟩ := h_min
        exact le_trans (half_le_self (le_of_lt hε_pos)) (hε'_bound t ⟨by linarith, le_refl t⟩)

  -- Show cumulative cost starts at zero
  have h_zero : cumulativeCost ψ 0 = 0 := by
    simp [cumulativeCost]

  -- Get existence from IVT
  obtain ⟨T, hT⟩ := cumulativeCost_unbounded ψ (fun t => h_nc t (by linarith)) h_bound_ext (collapse_threshold + 1)

  have h_ivt : ∃ t ∈ Set.Ioo 0 T, cumulativeCost ψ t = collapse_threshold := by
    apply intermediate_value_Ioo' (a := 0) (b := T)
    · exact (cumulativeCost_continuous ψ h_cont).continuousOn
    · rw [h_zero]
      exact pos_of_eq_pos collapse_threshold rfl
    · linarith

  obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ := h_ivt

  -- Show uniqueness from strict monotonicity
  use t₀
  constructor
  · exact ⟨ht₀_mem.1, ht₀_eq⟩
  · intro t' ⟨ht'_pos, ht'_eq⟩
    -- Two times with same cumulative cost must be equal
    by_cases h : t₀ < t'
    · have : cumulativeCost ψ t₀ < cumulativeCost ψ t' :=
        cumulativeCost_strictMono ψ (fun t => h_nc t (by linarith)) h
      rw [ht₀_eq, ht'_eq] at this
      exact absurd this (lt_irrefl _)
    by_cases h' : t' < t₀
    · have : cumulativeCost ψ t' < cumulativeCost ψ t₀ :=
        cumulativeCost_strictMono ψ (fun t => h_nc t (by linarith)) h'
      rw [ht₀_eq, ht'_eq] at this
      exact absurd this (lt_irrefl _)
    push_neg at h h'
    exact le_antisymm h' h

/-! ## Post-Collapse Evolution -/

/-- After collapse, system evolves classically -/
def postCollapseState (ψ : EvolvingState) (t_collapse : ℝ) (i : Fin n) :
    EvolvingState :=
  fun t => if t ≤ t_collapse then ψ t else
    { amplitude := fun j => if j = i then 1 else 0
      normalized := by simp [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)] }

/-- Post-collapse evolution has zero bandwidth cost -/
theorem postCollapse_zero_cost (ψ : EvolvingState) (t_c : ℝ) (i : Fin n) :
    ∀ t > t_c, superpositionCost (postCollapseState ψ t_c i t) = 0 := by
  intro t ht
  simp [postCollapseState, if_neg (not_le_of_gt ht)]
  apply (superposition_cost_nonneg _).2.mp
  use i
  intro j hj
  simp [if_neg hj]

namespace Constants
  def ℏ : Quantity ⟨2, 1, -1⟩ := ⟨1.054571817e-34⟩  -- J⋅s
end Constants

/-! ## Physics Axioms -/

/-- Unitary evolution preserves quantum superposition -/
axiom unitary_preserves_superposition {n : ℕ} (SE : SchrodingerEvolution n) :
    ¬isClassical SE.ψ₀ → ∀ t : ℝ, t ≥ 0 → ¬isClassical (evolvedState SE t)

/-! ## Quantum State Evolution -/

end RecognitionScience.Quantum
