#!/usr/bin/env python3
"""
Debug solver - minimal test of the verification process
"""

import os
import subprocess
import anthropic

API_KEY = os.environ.get("ANTHROPIC_API_KEY")
if not API_KEY:
    print("Error: ANTHROPIC_API_KEY environment variable not set")
    exit(1)

# Test 1: Check if lake env lean works
print("Test 1: Running lake env lean on TestSolver.lean")
result = subprocess.run(
    ['lake', 'env', 'lean', 'formal/TestSolver.lean'],
    capture_output=True,
    text=True
)
print(f"Return code: {result.returncode}")
print(f"Stderr: {result.stderr[:200] if result.stderr else 'None'}")
print()

# Test 2: Try to complete a simple proof
print("Test 2: Generating proof for 2 + 2 = 4")
client = anthropic.Anthropic(api_key=API_KEY)

response = client.messages.create(
    model="claude-3-5-sonnet-20241022",
    max_tokens=100,
    temperature=0,
    messages=[{
        "role": "user", 
        "content": "Generate a Lean 4 proof for: theorem two_plus_two : 2 + 2 = 4 := by\n\nProvide ONLY the proof tactics after 'by'. The answer should be very simple, likely just 'norm_num' or 'rfl'."
    }]
)

proof = response.content[0].text.strip()
print(f"Generated proof: {proof}")
print()

# Test 3: Update the file and verify
print("Test 3: Updating file with proof")
with open('formal/TestSolver.lean', 'r') as f:
    content = f.read()

# Replace the first sorry
new_content = content.replace('theorem two_plus_two : 2 + 2 = 4 := by\n  sorry', 
                              f'theorem two_plus_two : 2 + 2 = 4 := by\n  {proof}')

with open('formal/TestSolver_test.lean', 'w') as f:
    f.write(new_content)

# Verify the updated file
print("Verifying updated file...")
result = subprocess.run(
    ['lake', 'env', 'lean', 'formal/TestSolver_test.lean'],
    capture_output=True,
    text=True
)
print(f"Return code: {result.returncode}")
print(f"Stderr: {result.stderr[:200] if result.stderr else 'None'}")

# Clean up
os.remove('formal/TestSolver_test.lean')

print("\nDone!") 