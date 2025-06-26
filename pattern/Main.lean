/-
Recognition Science: Pattern Layer Main
======================================

This module imports and re-exports all Pattern Layer components,
serving as the main entry point for other modules.
-/

-- Core pattern concepts
import pattern.Core.PatternAxioms
import pattern.Core.TimelessExistence

-- Geometric organization
import pattern.Geometry.LogSpiralLattice

-- Pattern-Reality interface
import pattern.Interface.LockInMechanism
import pattern.Interface.SelectionPrinciple

-- Pattern library access
import pattern.Library.PatternRetrieval

-- Re-export main definitions
namespace RecognitionScience.Pattern

-- From Core
export Core (Pattern PatternCompleteness TimelessExistence)
export Core (pattern_distance exists_mathematically exists_physically)

-- From Geometry
export Geometry (q_star log_spiral PatternNode)
export Geometry (spiral_self_similarity optimal_scale_factor)

-- From Interface
export Interface (lock_in_threshold lock_in_time E_lock)
export Interface (LockInEvent selection_weight transition_allowed)

-- From Library
export Library (ConsciousState resonance retrieval_probability)
export Library (creativity_bandwidth enlightened_state)

end RecognitionScience.Pattern

-- Quick access to key theorems
namespace PatternLayer

open RecognitionScience.Pattern

-- The three key insights
theorem patterns_exist_timelessly := Core.TimelessExistence
theorem patterns_organize_on_spiral := Geometry.optimal_scale_factor
theorem patterns_crystallize_at_threshold := Interface.lock_in_conservation

-- The pattern-reality-consciousness triad
theorem pattern_reality_consciousness :
  ∃ (p : Pattern) (r : RealityState) (c : ConsciousState),
  was_selected_by c p ∧ manifested_as p r := by
  sorry -- TODO: prove the fundamental triad

end PatternLayer
