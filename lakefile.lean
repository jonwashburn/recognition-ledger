import Lake
open Lake DSL

package «recognition-ledger» where
  -- Package configuration
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «RecognitionScience» where
  -- Main library configuration
  srcDir := "formal"
  roots := #[`RecognitionScience]

-- Pattern module as part of main library
lean_lib «Pattern» where
  srcDir := "formal"
  roots := #[`RecognitionScience.Pattern]
  globs := #[.submodules `RecognitionScience.Pattern]

-- Test library
lean_lib «Tests» where
  srcDir := "test"
  roots := #[`Tests]

-- Mathlib dependency
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

-- Build configuration
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

-- Scripts
@[default_target]
lean_exe «recognition-ledger» where
  root := `Main
  supportInterpreter := true

-- Scripts for running Python solvers
script runUltimateSolver do
  IO.println "🚀 Running Ultimate Autonomous Solver (20 Claude Sonnet 4 agents)..."
  let exitCode ← IO.Process.spawn {
    cmd := "python3"
    args := #["formal/ultimate_autonomous_solver.py"]
  } >>= (·.wait)
  return exitCode

script runClaudeSolver do
  IO.println "🤖 Running Claude Sonnet Enhanced Solver..."
  let exitCode ← IO.Process.spawn {
    cmd := "python3"
    args := #["formal/claude_sonnet_enhanced_solver.py"]
  } >>= (·.wait)
  return exitCode

script runZeroSorrySolver do
  IO.println "✨ Running Zero Sorry Solver..."
  let exitCode ← IO.Process.spawn {
    cmd := "python3"
    args := #["formal/zero_sorry_solver.py"]
  } >>= (·.wait)
  return exitCode

script listSolvers do
  IO.println "📋 Available Solvers:"
  IO.println "───────────────────"
  IO.println "  • ultimate_autonomous_solver.py (20 agents)"
  IO.println "  • claude_sonnet_enhanced_solver.py"
  IO.println "  • zero_sorry_solver.py"
  IO.println "  • unified_completion_solver.py"
  IO.println "  • ... and 20+ more"
  return 0
