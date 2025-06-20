# AI Proof Solver for Recognition Science

This directory contains automated proof solvers for completing Lean 4 proofs in the Recognition Science project.

## Quick Start

See **[SOLVER_USAGE_GUIDE.md](SOLVER_USAGE_GUIDE.md)** for comprehensive documentation.

```bash
# Check current sorry count
find ../formal -name "*.lean" -type f -exec grep -E "(by sorry|:= sorry| sorry$)" {} \; | wc -l

# Run main solver
python3 solve_all_sorries.py

# For advanced solving
python3 advanced_claude4_solver.py ../formal/AxiomProofs.lean
```

## Key Scripts

- **`solve_all_sorries.py`** - Main solver, processes all files
- **`advanced_claude4_solver.py`** - Advanced solver with better patterns  
- **`simple_proof_filler.py`** - Basic tactics without API
- **`turbo_parallel_solver.py`** - Fast parallel processing

## Requirements

- Python 3.9+
- Anthropic API key (set as `ANTHROPIC_API_KEY`)
- Lean 4 installation
- Recognition Science project structure

## Current Status

- Using Claude Opus 4 model (slower but more capable)
- ~70 sorries remaining in the project
- Build remains clean after solver runs

See [SOLVER_USAGE_GUIDE.md](SOLVER_USAGE_GUIDE.md) for detailed usage instructions. 