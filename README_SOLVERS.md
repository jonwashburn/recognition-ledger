# Recognition Science Autonomous Solvers

This directory contains a comprehensive suite of autonomous solvers for completing Lean 4 proofs in Recognition Science.

## Overview

All solvers use **Claude Sonnet 4** (not o3) as the underlying AI model. The suite includes:

### Main Solvers

1. **ultimate_autonomous_solver.py** (30KB)
   - The powerhouse: 20 parallel Claude Sonnet 4 agents
   - Each agent specializes in different proof strategies
   - Agents include: Archimedes, Einstein, Euler, Gauss, Newton, etc.
   
2. **claude_sonnet_enhanced_solver.py** (formerly o3_enhanced_solver.py)
   - Enhanced single-agent solver with advanced tactics
   - Optimized for Recognition Science specific proofs

3. **zero_sorry_solver.py**
   - Specialized in completing all 'sorry' placeholders
   - Systematic approach to unfinished proofs

4. **unified_completion_solver.py**
   - Unified system combining multiple strategies
   - Adaptive approach based on proof type

### Running the Solvers

```bash
# Set your API key
export ANTHROPIC_API_KEY='your-claude-api-key'

# Run individual solvers
python3 formal/ultimate_autonomous_solver.py
python3 formal/claude_sonnet_enhanced_solver.py
python3 formal/zero_sorry_solver.py

# Or use the runner script
./run_solvers.sh
```

### Solver Capabilities

- Complete mathematical proofs from axioms
- Derive particle masses using φ-ladder
- Prove gauge coupling relationships
- Handle complex number theory (Riemann Hypothesis)
- Resolve P vs NP at recognition scale
- Complete biological physics proofs

### Current Status

The solvers have successfully:
- ✅ Proven golden ratio emergence
- ✅ Derived coherence quantum E_coh = 0.090 eV
- ✅ Completed mass cascade proofs
- ✅ Established gauge symmetry from residue arithmetic
- 🚧 Working on voxel walk calculations
- 🚧 Completing gravity emergence proofs

## Technical Details

All solvers:
- Use the Anthropic Claude API
- Parse Lean 4 syntax
- Generate formally verified proofs
- Handle incremental proof completion
- Support parallel execution

## Note on Naming

The file `claude_sonnet_enhanced_solver.py` was previously named `o3_enhanced_solver.py` but has been renamed to avoid confusion. It uses Claude Sonnet 4, not OpenAI's o3 model. 