/-
  Recognition Science: Ethics - Tests
  ==================================

  Executable tests for the Ethics framework.
  These tests verify basic properties with concrete values.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import Ethics.Curvature
import Ethics.Virtue
import Ethics.Measurement

namespace RecognitionScience.Ethics.Tests

open RecognitionScience.Ethics

/-!
# Concrete Test States
-/

/-- A highly positive curvature state (suffering) -/
def highDebtState : MoralState := {
  ledger := {
    entries := [],
    balance := 50,
    lastUpdate := 0
  },
  energy := { cost := 10 },
  valid := by norm_num
}

/-- A highly negative curvature state (joy/surplus) -/
def surplusState : MoralState := {
  ledger := {
    entries := [],
    balance := -30,
    lastUpdate := 0
  },
  energy := { cost := 20 },
  valid := by norm_num
}

/-- A balanced state (good) -/
def balancedState : MoralState := {
  ledger := {
    entries := [],
    balance := 0,
    lastUpdate := 0
  },
  energy := { cost := 15 },
  valid := by norm_num
}

/-!
# Basic Property Tests
-/

/-- Test: High debt state has positive curvature -/
example : κ highDebtState = 50 := by rfl

/-- Test: Surplus state has negative curvature -/
example : κ surplusState = -30 := by rfl

/-- Test: Balanced state has zero curvature -/
example : κ balancedState = 0 := by rfl

/-- Test: Balanced state is good -/
example : isGood balancedState := by
  simp [isGood, curvature, balancedState]

/-- Test: High debt state has suffering -/
example : suffering highDebtState = 50 := by
  simp [suffering, curvature, highDebtState]
  rfl

/-- Test: Surplus state has joy -/
example : joy surplusState = 30 := by
  simp [joy, curvature, surplusState]
  rfl

/-!
# Virtue Application Tests
-/

/-- Test: Love averages curvature -/
example :
  let (s1', s2') := Love highDebtState surplusState
  κ s1' = κ s2' := by
  simp [Love, curvature]

/-- Test: Love conserves total curvature -/
example :
  let (s1', s2') := Love highDebtState surplusState
  κ s1' + κ s2' = κ highDebtState + κ surplusState := by
  exact love_conserves_curvature highDebtState surplusState

/-- Test: Forgiveness reduces debtor curvature -/
example :
  let (c', d') := Forgive balancedState highDebtState 20
  κ d' < κ highDebtState := by
  simp [Forgive, curvature, highDebtState, balancedState]
  norm_num

/-- Test: Virtue training reduces curvature magnitude -/
example :
  Int.natAbs (κ (TrainVirtue Virtue.love highDebtState)) ≤
  Int.natAbs (κ highDebtState) := by
  exact virtue_training_reduces_curvature Virtue.love highDebtState

/-!
# Measurement Tests
-/

/-- Test: Neural measurement in range -/
example :
  let (κ_measured, _) := measureCurvature neuralCurvatureMeasurement 0.8
  abs κ_measured ≤ 50 := by
  simp [measureCurvature, neuralCurvatureMeasurement]
  have h := CurvatureMetric.bound (sig := CurvatureSignature.neural 40) 0.8
  exact h

/-- Test: Virtue recommendation for high personal and social curvature -/
example :
  let context := [highDebtState, highDebtState, highDebtState]
  recommendVirtue highDebtState context = Virtue.compassion := by
  simp [recommendVirtue, curvature, highDebtState]
  norm_num

/-- Test: Virtue recommendation for balanced state -/
example :
  let context := [balancedState, balancedState]
  recommendVirtue balancedState context = Virtue.creativity := by
  simp [recommendVirtue, curvature, balancedState]
  norm_num

/-!
# Community Dynamics Tests
-/

/-- Test community with mixed curvatures -/
def testCommunity : MoralCommunity := {
  members := [highDebtState, surplusState, balancedState],
  practices := [Virtue.love, Virtue.justice],
  coupling := 0.1
}

/-- Test: Virtue propagation affects all members -/
example :
  let evolved := PropagateVirtues testCommunity
  evolved.members.length = testCommunity.members.length := by
  simp [PropagateVirtues, testCommunity]

/-!
# Executable Verification Functions
-/

/-- Verify that love reduces variance for any two states -/
def verifyLoveReducesVariance (s1 s2 : MoralState) : Bool :=
  let (s1', s2') := Love s1 s2
  Int.natAbs (κ s1' - κ s2') ≤ Int.natAbs (κ s1 - κ s2)

/-- Run variance reduction test on concrete states -/
#eval verifyLoveReducesVariance highDebtState surplusState  -- Should be true

/-- Verify curvature bounds for measurements -/
def verifyCurvatureBounds (raw_neural : Real) : Bool :=
  let κ_val := CurvatureMetric.toκ (sig := CurvatureSignature.neural 40) raw_neural
  abs κ_val ≤ 50

/-- Test various neural measurements -/
#eval verifyCurvatureBounds 0.0   -- Should be true
#eval verifyCurvatureBounds 0.5   -- Should be true
#eval verifyCurvatureBounds 1.0   -- Should be true

/-- Verify virtue effectiveness at different scales -/
def verifyScaleDependence : Bool :=
  VirtueEffectiveness Virtue.love 1 > VirtueEffectiveness Virtue.justice 1 ∧
  VirtueEffectiveness Virtue.justice 10 > VirtueEffectiveness Virtue.love 10

#eval verifyScaleDependence  -- Should be true

/-!
# Integration Tests
-/

/-- Full moral evolution test -/
def moralEvolutionTest : Bool :=
  -- Start with high curvature
  let initial := highDebtState
  -- Apply love virtue
  let step1 := TrainVirtue Virtue.love initial
  -- Apply justice virtue
  let step2 := TrainVirtue Virtue.justice step1
  -- Check curvature decreased
  Int.natAbs (κ step2) < Int.natAbs (κ initial)

#eval moralEvolutionTest  -- Should be true

/-- Test complete virtue curriculum -/
def completeCurriculumTest : List Virtue → MoralState → Bool
  | [], s => true
  | v::vs, s =>
    let s' := TrainVirtue v s
    Int.natAbs (κ s') ≤ Int.natAbs (κ s) ∧ completeCurriculumTest vs s'

#eval completeCurriculumTest [Virtue.love, Virtue.wisdom, Virtue.compassion] highDebtState

end RecognitionScience.Ethics.Tests
