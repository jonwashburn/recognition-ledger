import RecognitionScience

/-- Main entry point for Recognition Science solver -/
def main : IO Unit := do
  IO.println "🌌 Recognition Science Autonomous Solver"
  IO.println "======================================="
  IO.println ""
  IO.println "Core Constants:"
  IO.println s!"• Golden ratio φ = (1+√5)/2"
  IO.println s!"• Coherence quantum E_coh = {E_coh} eV"
  IO.println s!"• Tick interval τ₀ = {τ₀} seconds"
  IO.println s!"• Eight-beat period = {eight_beat_period} seconds"
  IO.println ""
  IO.println "To run the autonomous solvers, use:"
  IO.println "  lake run runUltimateSolver"
  IO.println "  lake run runClaudeSolver"
  IO.println "  lake run runZeroSorrySolver"
  IO.println ""
  IO.println "For a list of all solvers: lake run listSolvers"
