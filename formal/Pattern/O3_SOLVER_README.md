# O3 Pattern Lemma Solvers

This directory contains two O3-based solvers for automatically proving lemmas in the Pattern module.

## Available Solvers

### 1. Basic O3 Solver (`o3_pattern_solver.py`)
- Simple, straightforward solver
- Processes lemmas one at a time
- Parallel file processing
- Good for initial attempts

### 2. Advanced O3 Solver (`o3_advanced_solver.py`)
- Batch processing for efficiency
- Retry logic with increasing temperature
- Proof caching to avoid re-solving
- Progress tracking and logging
- Cost estimation
- Complexity-based prioritization

## Setup

1. **Set up your API key**:
   ```bash
   export OPENAI_API_KEY='your-openai-api-key-here'
   ```
   
   Or create a `.env` file (copy from `env.example`):
   ```bash
   cp env.example .env
   # Edit .env with your actual API key
   ```

2. **Install requirements**:
   ```bash
   pip install -r requirements.txt
   ```

3. **Ensure you're in the Pattern directory**:
   ```bash
   cd recognition-ledger/formal/Pattern
   ```

## Usage

### Quick Start (Basic Solver)
```bash
# Set API key first
export OPENAI_API_KEY='your-api-key'

# Run solver
./run_o3_solver.sh
```

### Advanced Solver
```bash
# Set API key first
export OPENAI_API_KEY='your-api-key'

# Run advanced solver
python3 o3_advanced_solver.py
```

## Security Notes

⚠️ **NEVER commit API keys to version control!**

- Always use environment variables for API keys
- Add `.env` to your `.gitignore` file
- Use `env.example` as a template for others
- Consider using a secrets manager for production

## Features

### Basic Solver
- Detects lemma types (inequality, arithmetic, complex, etc.)
- Suggests appropriate tactics
- Saves results to `.solved.lean` files
- Parallel processing with configurable workers

### Advanced Solver
- **Batch Processing**: Solves multiple lemmas in one API call
- **Smart Retries**: Increases temperature on retries
- **Caching**: Remembers successful proofs across runs
- **Complexity Analysis**: Prioritizes simpler lemmas first
- **Enhanced Tactics**: Three-tier tactic database (primary/fallback/advanced)
- **Detailed Logging**: Full logs saved to `o3_solver.log`
- **Cost Tracking**: Estimates API usage costs

## Output

Both solvers create `.solved.lean` files with the proofs inserted:
- `BasicInequalities.solved.lean`
- `ComplexCalculus.solved.lean`
- `PrimeTheory.solved.lean`
- etc.

## Configuration

### Basic Solver
Edit `o3_pattern_solver.py`:
- `max_workers`: Number of parallel file processors (default: 3)

### Advanced Solver
Edit `o3_advanced_solver.py`:
- `max_retries`: Maximum attempts per lemma (default: 3)
- `batch_size`: Lemmas per batch (default: 5)

## Tactic Database

The solvers use specialized tactics for different lemma types:

| Type | Primary Tactics | Fallback | Advanced |
|------|----------------|----------|----------|
| inequality | norm_num, linarith | omega, ring | interval_cases |
| arithmetic | ring, field_simp | simp, abel | polyrith |
| complex | simp [Complex.ext_iff] | norm_num | convert |
| prime | exact Nat.Prime.two_prime | simp [Nat.Prime] | cases' |
| pattern | simp [FreeMonoid.one_def] | cases, induction | apply FreeMonoid.hom_ext |
| modular | simp [Nat.add_mod] | mod_cases | rw [Nat.mod_eq_of_lt] |
| set | simp [Set.mem_def] | intro, constructor | apply Set.Subset.antisymm |
| exponential | simp [Real.exp_zero] | positivity | rw [Real.exp_add] |
| convergence | apply Summable.of_norm | norm_num | rw [summable_norm_iff] |

## Monitoring Progress

### Basic Solver
- Real-time console output
- Per-file summaries
- Final success rate

### Advanced Solver
- Detailed logs in `o3_solver.log`
- Batch progress tracking
- Token usage and cost estimation
- Failed lemma listing

## Troubleshooting

1. **API Errors**: Check your API key and rate limits
2. **File Not Found**: Ensure you're in the Pattern directory
3. **Failed Proofs**: Check the logs for specific errors
4. **High Costs**: Reduce batch_size or use caching

## Cache Management

The advanced solver maintains a cache in `o3_proof_cache.json`:
- Automatically loaded on startup
- Updated after each batch
- Can be manually edited if needed

To clear the cache:
```bash
rm o3_proof_cache.json
```

## Example Output

```
================================================================================
ADVANCED O3 PATTERN LEMMA SOLVER
================================================================================
Found 42 lemmas to solve

Processing batch 1/9
  Attempt 1/3 for 5 lemmas
    ✓ Solved: one_lt_two
    ✓ Solved: exp_pos
    ✓ Solved: prime_two
    ✗ Failed: complex_balance_sum - No proof found in response
    ✓ Solved: pattern_grade_one

...

FINAL REPORT
================================================================================
✓ Lemmas/BasicInequalities.lean: 8/8 solved
⚠ Lemmas/ComplexCalculus.lean: 5/7 solved
✓ Lemmas/PrimeTheory.lean: 6/6 solved

TOTAL: 38/42 lemmas solved (90.5%)
Time elapsed: 124.3 seconds
Total tokens used: 45,231
Estimated cost: $0.90

⚠️  4 lemmas still need manual attention
```

## Next Steps

After running the solver:
1. Review the `.solved.lean` files
2. Test compilation with `lake build`
3. Manually fix any remaining `sorry` statements
4. Integrate solved files back into the main module 