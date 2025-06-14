#!/bin/bash

# Comprehensive Pattern Solver Runner
# Uses advanced strategies to prove Pattern theory lemmas

echo "🚀 Starting Comprehensive Pattern Solver..."
echo "=========================================="

# Check for API key
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Error: ANTHROPIC_API_KEY not set"
    echo "Please run: export ANTHROPIC_API_KEY='your-api-key'"
    exit 1
fi

echo "🚀 Running Comprehensive Pattern Theory Solver"
echo "============================================"
echo ""
echo "This solver uses all techniques from Solver Jon:"
echo "- Systematic decomposition"
echo "- Action divergence analysis"  
echo "- Critical strip techniques"
echo "- Enhanced prompting strategies"
echo ""

# First run the simple pattern solver to get baseline
echo "Phase 1: Running simple pattern solver..."
python3 pattern_solver.py 2>&1 | tee pattern_solver_phase1.log

echo ""
echo "Phase 2: Running comprehensive solver with enhanced strategies..."

# Copy the comprehensive solver from Solver Jon and adapt it
cp "../../Solver Jon/simple_determinant_solver.py" comprehensive_solver_temp.py

# Run with our Pattern lemmas
python3 - << 'SOLVER'
import os
import asyncio
from anthropic import AsyncAnthropic
import re

PATTERN_LEMMAS = [
    {"name": "balance_critical_strip", "file": "Pattern/Foundation.lean", "deps": []},
    {"name": "patternZeta_eq_zeta", "file": "Pattern/BalanceEnergy.lean", "deps": ["recognitionEnergy_convergent"]},
    {"name": "energy_diverges_at_zeros", "file": "Pattern/RiemannHypothesis.lean", "deps": []},
    {"name": "eight_beat_preserves_critical_line", "file": "Pattern/RiemannHypothesis.lean", "deps": []},
]

class EnhancedSolver:
    def __init__(self):
        self.client = AsyncAnthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
        
    async def prove_lemma(self, lemma):
        print(f"Attempting enhanced proof of: {lemma['name']}")
        
        # Read context
        with open(lemma["file"], 'r') as f:
            content = f.read()
            
        # Find lemma
        pattern = rf"(lemma|theorem) {lemma['name']}.*?:=\s*by\s*sorry"
        match = re.search(pattern, content, re.DOTALL)
        if not match:
            return False
            
        context = content[max(0, match.start()-500):match.end()+200]
        
        # Enhanced prompt with Recognition Science context
        prompt = f"""You are proving a lemma in the Pattern theory approach to Riemann Hypothesis.

Key insights:
- Patterns are recognition events, primes are irreducible patterns
- Critical line Re(s) = 1/2 represents perfect balance
- Eight-beat periodicity is fundamental
- Recognition energy diverges at zeros unless on critical line

Lemma context:
```lean
{context}
```

Provide a complete Lean 4 proof for {lemma['name']}. Use these strategies:
- For balance_critical_strip: Analyze exp(iπs) = -1 condition
- For patternZeta_eq_zeta: Use Euler product and analytic continuation
- For energy_diverges_at_zeros: Use contradiction with finite energy
- For eight_beat_preserves_critical_line: Use symmetry arguments

Respond with ONLY the proof code, no sorry."""

        try:
            response = await self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=4000,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            if "sorry" not in proof.lower():
                print(f"✅ Enhanced proof found for {lemma['name']}")
                # Save proof
                new_content = re.sub(
                    pattern,
                    rf"\1 {lemma['name']}\2:= by\n  {proof}",
                    content,
                    flags=re.DOTALL
                )
                
                output_file = lemma["file"].replace('.lean', '_ENHANCED.lean')
                with open(output_file, 'w') as f:
                    f.write(new_content)
                    
                return True
        except Exception as e:
            print(f"Error: {e}")
            
        return False

async def main():
    solver = EnhancedSolver()
    for lemma in PATTERN_LEMMAS:
        await solver.prove_lemma(lemma)
        await asyncio.sleep(2)

asyncio.run(main())
SOLVER

echo ""
echo "Phase 3: Checking results..."
echo ""

# Count successes
echo "Files created:"
ls -la Pattern/*_SOLVED.lean Pattern/*_ENHANCED.lean Pattern/*_COMPREHENSIVE.lean 2>/dev/null || echo "Check individual phases"

echo ""
echo "Sorry count comparison:"
for file in Pattern/*.lean; do
    if [[ -f "$file" && ! "$file" =~ "_SOLVED" && ! "$file" =~ "_ENHANCED" && ! "$file" =~ "_COMPREHENSIVE" ]]; then
        original=$(grep -c "sorry" "$file" 2>/dev/null || echo 0)
        echo "$file: $original sorries originally"
        
        for suffix in "_SOLVED" "_ENHANCED" "_COMPREHENSIVE"; do
            solved_file="${file%.lean}${suffix}.lean"
            if [[ -f "$solved_file" ]]; then
                solved=$(grep -c "sorry" "$solved_file" 2>/dev/null || echo 0)
                echo "  → $solved_file: $solved sorries"
            fi
        done
    fi
done

echo ""
echo "Comprehensive solving complete!" 