# Recognition Science Lean Proof Solver Usage Guide

## Overview
This directory contains various automated proof solvers for completing `sorry` statements in Lean 4 files. The solvers use Claude AI (Opus 4) to generate proofs and validate them through compilation.

## Quick Start

### 1. First Time Setup
```bash
# Ensure you have API key set
export ANTHROPIC_API_KEY="your-api-key"

# Check current sorry count
cd .. && find formal -name "*.lean" -type f -exec grep -E "(by sorry|:= sorry| sorry$)" {} \; | wc -l
```

### 2. Recommended Workflow

#### Step 1: Start with Simple Proofs
```bash
# Try simple tactics first (no API needed)
python3 simple_proof_filler.py ../formal/YourFile.lean

# For numerical proofs
python3 simple_numerical_prover.py
```

#### Step 2: Run the Main Solver
```bash
# Solve all files with sorries
python3 solve_all_sorries.py

# Or target specific files
python3 solve_all_sorries.py --attempts 3
```

#### Step 3: Advanced Solving
```bash
# For stubborn proofs, use advanced solver
python3 advanced_claude4_solver.py ../formal/AxiomProofs.lean

# Or use ultimate solver for comprehensive attempts
python3 ultimate_solver.py
```

## Solver Scripts by Category

### Basic Solvers (Start Here)
- **`simple_proof_filler.py`** - Tries basic tactics (rfl, simp, norm_num) without API
- **`simple_numerical_prover.py`** - Generates proofs for numerical theorems
- **`tactic_filter.py`** - Quick tactic attempts with timeout

### Main Workhorses
- **`solve_all_sorries.py`** - Primary solver that processes all files with sorries
- **`turbo_parallel_solver.py`** - Fast parallel solver with 4 workers
- **`advanced_claude4_solver.py`** - Advanced solver with better context and patterns

### Specialized Solvers
- **`ultimate_solver.py`** - Tries multiple strategies per proof
- **`enhanced_recognition_solver.py`** - Recognition Science specific context
- **`iterative_claude4_solver.py`** - Learns from successes/failures

### Batch Processing
- **`batch_solver.py`** - Process multiple files in sequence
- **`parallel_solver.py`** - Multi-threaded solving
- **`aggressive_solver.py`** - Runs all solvers aggressively

### Manual/Interactive
- **`manual_recognition_solver.py`** - Generates proofs for manual review
- **`file_specific_solver.py`** - Target specific files
- **`targeted_proof_completer.py`** - Focus on specific proof patterns

## Key Features

### Proof Cache System
- Successful proofs are cached in `proof_cache.json`
- Cache includes fingerprints for similar theorem detection
- Clear cache with: `mv proof_cache.json proof_cache.json.bak && echo '{}' > proof_cache.json`

### Compile Validation
- All proofs are tested by compilation before applying
- Failed proofs are automatically reverted
- Build status checked after each batch

### Backup System
- Automatic backups created before changes
- Backups stored in `backups/` directory
- Restore with: `cp backups/[timestamp]/* ../formal/`

## Typical Session Example

```bash
# 1. Check starting point
cd AI_ProofSolver_RS
find ../formal -name "*.lean" -type f -exec grep -E "(by sorry|:= sorry| sorry$)" {} \; | wc -l
# Output: 70 sorries

# 2. Run simple tactics first
python3 simple_proof_filler.py ../formal/Core/GoldenRatio.lean
# May resolve 0-5 trivial proofs

# 3. Run main solver
python3 solve_all_sorries.py
# Typically resolves 10-30 proofs per run

# 4. For remaining difficult proofs
python3 advanced_claude4_solver.py ../formal/AxiomProofs.lean
# May resolve 2-10 more complex proofs

# 5. Check progress
cd .. && lake build
find formal -name "*.lean" -type f -exec grep -E "(by sorry|:= sorry| sorry$)" {} \; | wc -l
# Output: 50 sorries (20 resolved!)

# 6. Commit progress
git add -A && git commit -m "Resolved 20 proofs - build successful" && git push
```

## Troubleshooting

### "No sorries found"
- Some solvers look for specific patterns
- Try `solve_all_sorries.py` which finds all sorries

### Cache-only results
- Clear cache to force fresh attempts
- Or use `--force-llm` flag where available

### Build failures
- Check `lake build` after each solver run
- Revert failed changes from backups

### API timeouts
- Claude Opus 4 is slower but more capable
- Use `--timeout 60` for longer waits
- Reduce batch size with `--max-proofs 5`

## Performance Tips

1. **Start simple**: Use non-API solvers first
2. **Batch wisely**: 5-10 proofs at a time for Opus 4
3. **Target files**: Focus on files with few sorries first
4. **Monitor progress**: Check sorry count regularly
5. **Commit often**: Save progress after successful runs

## Current Limitations

- Some advanced mathematical proofs require manual intervention
- Corrupted text patterns need manual cleanup
- Cache can become stale - clear periodically
- Opus 4 is slower than Sonnet but more capable

## Model Configuration

All solvers now use Claude Opus 4:
```python
model="claude-opus-4-20250514"
```

To update back to Sonnet (faster but less capable):
```python
model="claude-3-5-sonnet-20241022"
``` 