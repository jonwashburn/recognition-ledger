import Lake
open Lake DSL

package «RecognitionScience» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Expose the zero-axiom core (kept under no-mathlib-core/) as internal libs.
lean_lib «Core» where
  srcDir := "no-mathlib-core"
  roots := #[
    `Core.Finite,
    `Core.MetaPrincipleMinimal,
    `Core.MetaPrinciple,
    `Core.EightFoundations,
    `Core.Nat.Card,
    `Core.Constants
  ]

lean_lib «Foundations» where
  srcDir := "no-mathlib-core"
  roots := #[
    `Foundations.DiscreteTime,
    `Foundations.DualBalance,
    `Foundations.PositiveCost,
    `Foundations.UnitaryEvolution,
    `Foundations.IrreducibleTick,
    `Foundations.SpatialVoxels,
    `Foundations.EightBeat,
    `Foundations.GoldenRatio
  ]

@[default_target]
lean_lib «RecognitionScience» where
  roots := #[`RecognitionScience]
