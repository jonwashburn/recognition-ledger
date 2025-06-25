# README for AI Agents

## Identity
You are using AI_ProofSolver_RS, a Recognition Science Lean 4 proof automation system. Your task: resolve `sorry` placeholders in formal mathematical proofs.

## Capabilities
- Resolve 37% of sorries automatically
- 100% success rate on simple numerical proofs
- Cache successful proofs for reuse
- Parallel processing for speed
- Maintain compilation success

## Primary Workflow
```bash
cd AI_ProofSolver_RS
export ANTHROPIC_API_KEY=<key>
python3 simple_proof_filler.py   # Try simple tactics first
python3 solve_all_sorries.py     # Main solver
python3 advanced_claude4_solver.py # For stubborn proofs
```

## Decision Tree
```
if simple_proofs:
    use simple_proof_filler.py
if all_files:
    use solve_all_sorries.py
if specific_file:
    use advanced_claude4_solver.py <file>
if aggressive:
    use run_aggressive.py
if manual_review:
    use manual_recognition_solver.py
```

## Recognition Science Domain Knowledge
- Meta-principle: "Nothing cannot recognize itself"
- Golden ratio φ = (1+√5)/2 central to all physics
- Eight-beat period emerges from recognition constraints
- All masses on φ-ladder: electron=φ^0, muon=φ^5, tau=φ^10
- Coherence energy E_coh = 0.090 eV
- Fundamental tick τ = 7.33×10^-15 s

## Proof Strategy Ranking
1. Try `norm_num` first (60% success)
2. Try `unfold <term>; norm_num` (20% success)
3. Try `rfl` for definitions (10% success)
4. Use AI generation (10% success)

## File Categories
- **Easy**: Philosophy/, Journal/ (mostly norm_num)
- **Medium**: Numerics/, Core/ (unfold + norm_num)
- **Hard**: AxiomProofs, MetaPrinciple (complex proofs)
- **Skip**: Files with "wrong order of magnitude" comments

## Cache Intelligence
- Fingerprints theorems by structure
- 30% hit rate after population
- Reuses proofs across similar theorems
- Persistent between sessions

## Constraints
- Cannot resolve proofs marked as mathematically incorrect
- Cannot compute very large exponents (φ^32+)
- Cannot handle undefined terms
- Must maintain successful compilation

## Output Format
```
============================================================
ULTIMATE SOLVER: FileName.lean
============================================================
Found N sorries
--- Sorry 1/N: theorem_name ---
✓ Resolved!
SUMMARY:
  Resolved: X/N
  Cache hits: Y
  Success rate: Z%
```

## Integration with Lean Project
- Works with Recognition Science ledger format
- Expects `lake build` to work
- Modifies .lean files in place
- Creates .backup files automatically

## Performance Expectations
- Simple proofs: <1 second each
- Complex proofs: 2-5 seconds each
- Cache hits: instant
- Parallel: 3x speedup

## Error Recovery
- All changes backed up
- Failed proofs skipped
- Build checked after batch
- Cache corruption handled

## Success Metrics
- Using Claude Opus 4 (slower but more capable)
- 173 → 70 sorries (60% reduction achieved)
- 100% build success maintained
- 24 proofs cached
- Manual proof editing also effective 