#!/usr/bin/env python3
"""
Recognition Science Focused Solver - One Proof at a Time
Tests individual proofs with full RS context
"""

import os
import re
import json
import subprocess
import time
from pathlib import Path
from openai import OpenAI
import shutil

# Get API key
api_key = os.environ.get('OPENAI_API_KEY')
if not api_key:
    print("Error: OPENAI_API_KEY not set")
    exit(1)

client = OpenAI(api_key=api_key)

# Recognition Science Context from source_code_June-26.txt
RS_CONTEXT = """
# RECOGNITION SCIENCE CORE PRINCIPLES

## THE EIGHT AXIOMS
1. DISCRETE RECOGNITION - Reality updates only at countable tick moments
2. DUAL-RECOGNITION BALANCE - Every tick satisfies: L = J·L⁻¹·J where J² = identity
3. POSITIVITY OF RECOGNITION COST - C(S) ≥ 0, equals 0 only for vacuum
4. UNITARY LEDGER EVOLUTION - Information conserved: L† = L⁻¹
5. IRREDUCIBLE TICK INTERVAL - τ₀ = 7.33 fs fundamental time quantum
6. IRREDUCIBLE SPATIAL VOXEL - Space quantized at L₀ = 0.335 nm
7. EIGHT-BEAT CLOSURE - L⁸ commutes with all symmetries
8. SELF-SIMILARITY - Scale operator Σ with λ = φ (golden ratio)

## KEY CONSTANTS (ALL DERIVED)
- E_coh = 0.090 eV (coherence quantum, NOT a free parameter)
- φ = 1.6180339887... (golden ratio, unique from J(φ) = φ)
- τ₀ = 1/(8 log φ) = 7.33 fs (from 8-beat requirement)
- All masses: E_r = E_coh × φ^r (no Yukawa couplings)

## DERIVATION PATTERNS

### Meta-Principle → Discrete Time
"Nothing cannot recognize itself" is the starting point.
- If nothing could recognize itself, it would be something (contradiction)
- Therefore something must exist that CAN recognize
- Recognition requires distinguishing states (before/after)
- Continuous time → infinite states between any two moments
- Infinite states → infinite information → impossible
- Therefore time MUST be discrete

### Discrete → Dual Balance
- Discrete updates need consistency condition
- Simplest non-trivial: binary (debit/credit)
- Balance requirement: total debt = 0
- Leads to J² = 1 (swap debits/credits twice = identity)

### Dual Balance → Positive Cost
- If recognition had zero cost, infinite recognitions possible
- This violates finiteness from discrete time
- Therefore cost > 0 for all non-vacuum states
- Positive cost drives arrow of time

### Cost Minimization → Golden Ratio
- Cost functional J(x) = ½(x + 1/x) 
- Minimized when dJ/dx = 0
- This gives x² - x - 1 = 0
- Solution: x = φ = (1+√5)/2

### Eight-Beat from Dimensionality
- 3 spatial dimensions + 1 time = 4 dimensions
- Each dimension has 2 directions (+/-)
- Phase space: 2^4 = 16 states
- Conservation constraint reduces by factor 2
- Result: 8 independent states per cycle

## PROOF STRATEGIES

1. NECESSITY NOT SUFFICIENCY
Bad: "Bool works for binary" 
Good: "Binary is the ONLY non-trivial finite system"

2. USE THE CASCADE
Most quantities follow E_r = E_coh × φ^r
Check if the sorry involves energy/mass/frequency

3. EIGHT-BEAT CONSTRAINTS
Anything cyclic must complete in 8 ticks
Phase relationships: 2π/8 = 45° increments

4. LEDGER BALANCE
Every process must maintain Σdebits = Σcredits
No net creation or destruction

5. RECOGNITION LIMITS
Minimum time: τ₀ = 7.33 fs
Minimum energy: E_coh = 0.090 eV
Minimum length: L₀ = 0.335 nm
"""

class FocusedSolver:
    def __init__(self, project_root):
        self.project_root = Path(project_root)
        
    def extract_theorem_context(self, file_path, theorem_name):
        """Extract the specific theorem and its context"""
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Find the theorem - look for theorems containing sorry in their proof
        # This pattern is more flexible to handle sorry inside proof blocks
        pattern = rf'(theorem|lemma)\s+{theorem_name}.*?:=.*?sorry'
        match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
        
        if not match:
            return None, None
            
        theorem_text = match.group(0)
        
        # Get some context before the theorem
        start = max(0, match.start() - 500)
        context_before = content[start:match.start()]
        
        # Extract imports
        imports = re.findall(r'^import\s+(.+)$', content, re.MULTILINE)
        
        return theorem_text, {
            'imports': imports,
            'context_before': context_before,
            'full_content': content
        }
        
    def generate_proof(self, theorem_text, context, iteration=0):
        """Generate proof with Recognition Science context"""
        
        prompt = f"""You are proving a theorem in Recognition Science using Lean 4.

{RS_CONTEXT}

## AVAILABLE CONTEXT

Imports:
{chr(10).join(context['imports'])}

Recent definitions:
{context['context_before']}

## THEOREM TO PROVE

{theorem_text}

## YOUR TASK

Generate a Lean 4 proof to replace 'sorry'. 

Remember:
1. Use Recognition Science principles (8 axioms, golden ratio, etc.)
2. E_coh = 0.090 eV is DERIVED, not a free parameter
3. All masses follow E_r = E_coh × φ^r
4. Eight-beat cycle constrains all periodic phenomena
5. Start simple, use calc for equations, exact for direct applications

Output ONLY the proof code that replaces 'sorry'.
Do not include the theorem declaration."""

        try:
            response = client.chat.completions.create(
                model="gpt-4o",
                messages=[
                    {"role": "system", "content": "You are an expert in Recognition Science and Lean 4. Output only valid Lean proof code."},
                    {"role": "user", "content": prompt}
                ],
                temperature=0.1,  # Low temperature for consistency
                max_tokens=4000  # Maximum tokens for complete proofs
            )
            
            proof = response.choices[0].message.content.strip()
            
            # Clean the proof
            if proof.startswith('by'):
                proof = proof[2:].strip()
                
            # Remove any markdown
            proof = re.sub(r'```lean?\s*', '', proof)
            proof = re.sub(r'```\s*', '', proof)
            
            return proof
            
        except Exception as e:
            print(f"Error calling API: {e}")
            return None
            
    def test_proof(self, file_path, theorem_name, proof):
        """Test if the proof compiles"""
        # Read file
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Find the theorem and its sorry
        pattern = rf'((theorem|lemma)\s+{theorem_name}.*?:=.*?)sorry'
        match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
        
        if not match:
            return False, "Could not find theorem with sorry", None
            
        # Replace the sorry with our proof
        # Keep everything before sorry, add our proof
        before_sorry = match.group(1)
        
        # Check if we need proper indentation
        lines = before_sorry.split('\n')
        last_line = lines[-1] if lines else ""
        indent = len(last_line) - len(last_line.lstrip())
        
        # Format the proof with proper indentation
        proof_lines = proof.split('\n')
        indented_proof = '\n'.join(' ' * indent + line if line.strip() else line 
                                  for line in proof_lines)
        
        # Create the replacement
        replacement = before_sorry + indented_proof
        
        # Replace in content
        new_content = content[:match.start()] + replacement + content[match.end():]
        
        # Write to temp file - but use the original file name
        # This avoids Lake module path issues
        backup_file = file_path.with_suffix('.backup')
        
        try:
            # Backup original
            shutil.copy(file_path, backup_file)
            
            # Write new content to original file
            with open(file_path, 'w') as f:
                f.write(new_content)
            
            # Compile using Lake
            result = subprocess.run(
                ['lake', 'build', 'foundation'],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            success = result.returncode == 0
            
            # Combine stdout and stderr for better error reporting
            output = ""
            if result.stdout:
                output += "STDOUT:\n" + result.stdout + "\n"
            if result.stderr:
                output += "STDERR:\n" + result.stderr
            
            error = output if not success else ""
            
            if not success:
                # Restore original on failure
                shutil.copy(backup_file, file_path)
                
            # Clean up backup
            backup_file.unlink()
            
            return success, error, new_content
            
        except Exception as e:
            # Restore original on any error
            if backup_file.exists():
                shutil.copy(backup_file, file_path)
                backup_file.unlink()
            return False, str(e), None
            
    def solve_single_theorem(self, file_path, theorem_name, max_attempts=3):
        """Solve a single theorem with multiple attempts"""
        print(f"\n{'='*60}")
        print(f"Solving: {theorem_name} in {file_path.name}")
        print(f"{'='*60}")
        
        # Extract theorem
        theorem_text, context = self.extract_theorem_context(file_path, theorem_name)
        
        if not theorem_text:
            print(f"❌ Could not find theorem {theorem_name}")
            return False
            
        print(f"\nTheorem:")
        print(theorem_text)
        
        for attempt in range(max_attempts):
            print(f"\n🔄 Attempt {attempt + 1}/{max_attempts}")
            
            # Generate proof
            proof = self.generate_proof(theorem_text, context, attempt)
            if not proof:
                continue
                
            print(f"\nGenerated proof:")
            print("-" * 40)
            print(proof)
            print("-" * 40)
            
            # Test it
            success, error, new_content = self.test_proof(file_path, theorem_name, proof)
            
            if success:
                print(f"\n✅ SUCCESS! Proof compiles correctly.")
                
                # Save the successful proof
                with open(file_path, 'w') as f:
                    f.write(new_content)
                
                return True
            else:
                print(f"\n❌ Compilation failed:")
                # Extract key error
                if 'error:' in error:
                    for line in error.split('\n'):
                        if 'error:' in line.lower():
                            print(f"  {line.strip()}")
                    # Also print a bit more context
                    print("\nFull error output:")
                    print(error[:500] + "..." if len(error) > 500 else error)
                else:
                    print(f"  {error[:500]}..." if len(error) > 500 else error)
                    
        print(f"\n❌ Failed after {max_attempts} attempts")
        return False

def compile_and_test(file_path, new_proof):
    """
    Compile the file with the new proof and check for errors.
    """
    # Create a backup of the original file
    backup_path = file_path + ".backup"
    shutil.copy2(file_path, backup_path)
    
    try:
        # Read the file content
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Replace the sorry with the generated proof
        # More sophisticated replacement that handles the comment
        pattern = r'sorry\s*--[^\n]*'
        new_content = re.sub(pattern, new_proof.strip(), content, count=1)
        
        # Write the modified content
        with open(file_path, 'w') as f:
            f.write(new_content)
        
        # Navigate to foundation directory and compile
        original_dir = os.getcwd()
        foundation_dir = os.path.join(os.path.dirname(file_path), '..', '..', '..')
        os.chdir(foundation_dir)
        
        # Run lake build
        result = subprocess.run(
            ['lake', 'build'],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        os.chdir(original_dir)
        
        if result.returncode == 0:
            return True, "Compilation successful!"
        else:
            error_msg = result.stderr if result.stderr else result.stdout
            return False, error_msg
            
    except subprocess.TimeoutExpired:
        return False, "Compilation timed out"
    except Exception as e:
        return False, f"Error during compilation: {str(e)}"
    finally:
        # Restore the original file
        shutil.move(backup_path, file_path)

def main():
    # Get project root
    current_dir = Path.cwd()
    project_root = current_dir.parent.parent  # Go up to repo root
    
    solver = FocusedSolver(project_root)
    
    # Start with ONE specific theorem to test
    test_cases = [
        {
            'file': 'foundation/Core/Derivations/YangMillsMassGap.lean',
            'theorem': 'mass_gap_value'
        }
    ]
    
    print("🎯 Recognition Science Focused Solver")
    print("Testing one proof at a time with full RS context")
    print("-" * 60)
    
    for test in test_cases:
        file_path = project_root / test['file']
        if file_path.exists():
            success = solver.solve_single_theorem(file_path, test['theorem'])
            
            if success:
                print("\n🎉 Success! Let's test another one...")
                # Add more test cases gradually
                test_cases.append({
                    'file': 'foundation/Core/Derivations/YangMillsMassGap.lean',
                    'theorem': 'mass_gap_value'
                })
        else:
            print(f"⚠️ File not found: {test['file']}")
            
    print("\n" + "="*60)
    print("Testing complete!")

if __name__ == "__main__":
    main() 