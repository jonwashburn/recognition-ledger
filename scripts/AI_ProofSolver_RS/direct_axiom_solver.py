#!/usr/bin/env python3
"""
Direct solver for recognition_fixed_points_corrected in AxiomProofs.lean
"""

import os
import sys
from openai import OpenAI
from pathlib import Path

def get_proof_for_recognition_fixed_points():
    """Generate a proof for the recognition_fixed_points_corrected theorem"""
    
    # Set up OpenAI client
    api_key = os.environ.get('OPENAI_API_KEY')
    if not api_key:
        print("❌ Error: OPENAI_API_KEY not set")
        return None
    
    client = OpenAI(api_key=api_key)
    
    # The theorem we're trying to prove
    theorem = """
theorem recognition_fixed_points_corrected :
  ∀ (s : State), (J s = s) ↔ (s = vacuum ∨ s = φ_state)
"""
    
    # Context about the problem
    context = """
In Recognition Science:
- J is the recognition operator (cost functional)
- J(x) = (x + 1/x)/2 for positive x
- vacuum is the zero/empty state
- φ_state is the golden ratio state where φ = (1 + √5)/2
- The theorem states that J has exactly two fixed points: vacuum and φ_state
"""
    
    prompt = f"""You are a Lean 4 expert. Complete this proof:

{theorem} := by

Context: {context}

The proof should show:
1. Forward direction: If J s = s, then s must be vacuum or φ_state
2. Backward direction: If s is vacuum or φ_state, then J s = s

Generate ONLY the Lean 4 proof code that goes after 'by'. No explanations."""
    
    try:
        response = client.chat.completions.create(
            model="gpt-4-turbo-preview",
            messages=[
                {"role": "system", "content": "You are a Lean 4 proof assistant. Generate only valid Lean 4 code."},
                {"role": "user", "content": prompt}
            ],
            max_tokens=1000,
            temperature=0.2
        )
        
        proof = response.choices[0].message.content.strip()
        
        # Clean up the proof
        if proof.startswith("```"):
            proof = proof.split("```")[1]
            if proof.startswith("lean"):
                proof = proof[4:].strip()
        
        return proof
        
    except Exception as e:
        print(f"❌ API Error: {e}")
        return None

def apply_proof_to_file(proof):
    """Apply the generated proof to AxiomProofs.lean"""
    
    file_path = Path("formal/AxiomProofs.lean")
    if not file_path.exists():
        print(f"❌ File not found: {file_path}")
        return False
    
    # Read the file
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Find the theorem
    import re
    pattern = r'(theorem recognition_fixed_points_corrected\s*:.*?:=\s*by)\s+(.*?)(?=\n(?:theorem|lemma|def|end|--|\Z))'
    
    match = re.search(pattern, content, re.DOTALL)
    if not match:
        print("❌ Could not find recognition_fixed_points_corrected theorem")
        return False
    
    # Extract the current proof content
    theorem_start = match.group(1)
    current_proof = match.group(2)
    
    # Count the sorries in the current proof
    sorry_count = current_proof.count('sorry')
    print(f"📊 Found {sorry_count} sorries in current proof")
    
    # Create the new proof
    new_theorem = f"{theorem_start}\n  {proof}"
    
    # Replace in content
    old_full = match.group(0)
    new_content = content.replace(old_full, new_theorem)
    
    # Backup and save
    backup_path = file_path.with_suffix('.backup_direct')
    with open(backup_path, 'w') as f:
        f.write(content)
    
    with open(file_path, 'w') as f:
        f.write(new_content)
    
    print(f"✅ Applied proof to {file_path}")
    print(f"📋 Backup saved to {backup_path}")
    
    return True

def main():
    print("🎯 Direct Recognition Fixed Points Solver")
    print("=" * 50)
    
    print("\n📝 Generating proof for recognition_fixed_points_corrected...")
    proof = get_proof_for_recognition_fixed_points()
    
    if not proof:
        print("❌ Failed to generate proof")
        return
    
    print("\n✨ Generated proof:")
    print("-" * 40)
    print(proof[:500] + "..." if len(proof) > 500 else proof)
    print("-" * 40)
    
    print("\n📄 Applying to formal/AxiomProofs.lean...")
    success = apply_proof_to_file(proof)
    
    if success:
        print("\n✅ Success! Next steps:")
        print("1. Run 'lake build' to check if the proof compiles")
        print("2. If it fails, check the error and iterate")
    else:
        print("\n❌ Failed to apply proof")

if __name__ == "__main__":
    main() 