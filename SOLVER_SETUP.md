# Solver Setup Instructions

## Environment Setup

To use the automated proof solvers, you need to set up your API key:

1. **Set the environment variable**:
   ```bash
   export ANTHROPIC_API_KEY="your-api-key-here"
   ```

2. **Or create a .env file** (recommended):
   ```bash
   echo 'ANTHROPIC_API_KEY=your-api-key-here' > .env
   ```

3. **Never commit API keys to git!**

## Running the Solvers

Once your environment is set up:

```bash
# Simple solver for test theorems
python3 formal/simple_working_solver.py

# Universe-level solver for all proofs
python3 formal/universe_proof_solver.py

# Improved solver with better verification
python3 formal/improved_universe_solver.py
```

## Security Note

The API key should never be hardcoded in source files. Always use environment variables. 