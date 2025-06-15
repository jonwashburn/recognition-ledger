#!/usr/bin/env python3
"""
Simple Working Solver - Focus on getting proofs that compile
"""

import os
import subprocess
import anthropic
import json
from datetime import datetime

# Get API key from environment
API_KEY = os.environ.get("ANTHROPIC_API_KEY")
if not API_KEY:
    print("Error: ANTHROPIC_API_KEY environment variable not set")
    exit(1)

print("🌌 Simple Working Solver for Recognition Science")
print("=" * 50)

client = anthropic.Anthropic(api_key=API_KEY)

# Target simple theorems in TestSolver.lean
theorems = [
    ("two_plus_two", "2 + 2 = 4", "This should be provable with 'rfl' or 'norm_num'"),
    ("five_gt_three", "5 > 3", "This should be provable with 'norm_num'"),
    ("E_coh_pos", "E_coh > 0", "E_coh is defined as 0.090, use 'unfold E_coh' then 'norm_num'")
]

completed = 0
results = []

for name, statement, hint in theorems:
    print(f"\n[{name}] Proving: {statement}")
    
    # Generate proof
    prompt = f"""Generate a Lean 4 proof for:
theorem {name} : {statement} := by
  sorry

{hint}

Provide ONLY the proof tactics to replace 'sorry'. Common tactics:
- rfl (reflexivity)
- norm_num (normalize numbers)
- unfold <definition> (expand definition)
- simp (simplify)

Just give the tactics, nothing else."""

    response = client.messages.create(
        model="claude-3-5-sonnet-20241022",
        max_tokens=200,
        temperature=0,
        messages=[{"role": "user", "content": prompt}]
    )
    
    proof = response.content[0].text.strip()
    print(f"  Generated: {proof}")
    
    # Read file
    with open('formal/TestSolver.lean', 'r') as f:
        content = f.read()
    
    # Find and replace the theorem
    old_theorem = f"theorem {name} : {statement} := by\n  sorry"
    new_theorem = f"theorem {name} : {statement} := by\n  {proof}"
    
    if old_theorem in content:
        # Update file
        new_content = content.replace(old_theorem, new_theorem)
        with open('formal/TestSolver.lean', 'w') as f:
            f.write(new_content)
        
        # Verify
        result = subprocess.run(
            ['lake', 'env', 'lean', 'formal/TestSolver.lean'],
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            print(f"  ✅ Success! Proof verified.")
            completed += 1
            results.append({
                'theorem': name,
                'proof': proof,
                'status': 'success'
            })
        else:
            print(f"  ❌ Failed. Reverting...")
            # Revert
            with open('formal/TestSolver.lean', 'w') as f:
                f.write(content)
            results.append({
                'theorem': name,
                'proof': proof,
                'status': 'failed',
                'error': result.stderr[:200] if result.stderr else result.stdout[:200]
            })
    else:
        print(f"  ⚠️ Could not find theorem in file")

# Summary
print(f"\n{'='*50}")
print(f"Completed: {completed}/{len(theorems)}")
print(f"Success rate: {completed/len(theorems)*100:.0f}%")

# Save results
with open('simple_solver_results.json', 'w') as f:
    json.dump({
        'timestamp': datetime.now().isoformat(),
        'completed': completed,
        'total': len(theorems),
        'results': results
    }, f, indent=2)

print("\nResults saved to simple_solver_results.json") 