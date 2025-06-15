import RecognitionScience

open RecognitionScience

/-- Main entry point for Recognition Science solver -/
def main : IO Unit := do
  IO.println "🌌 Recognition Science Autonomous Solver"
  IO.println "======================================="
  IO.println ""
  IO.println "Core Constants:"
  IO.println s!"• Golden ratio φ = (1+√5)/2"
  IO.println "• Coherence quantum E_coh = 0.090 eV"
  IO.println "• Tick interval τ₀ = 7.33e-15 seconds"
  IO.println "• Eight-beat period = 5.864e-14 seconds"
  IO.println ""
  IO.println "To run the autonomous solvers, use:"
  IO.println "  lake run runUltimateSolver"
  IO.println "  lake run runClaudeSolver"
  IO.println "  lake run runZeroSorrySolver"
  IO.println ""
  IO.println "For a list of all solvers: lake run listSolvers"
