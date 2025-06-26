#!/usr/bin/env python3
"""
Ethics Module O3 Solver - Adapted from Navier-Stokes O3 Solver
Optimized for ethics module specific patterns and challenges
"""

import os
import re
import json
import subprocess
import shutil
from pathlib import Path
from datetime import datetime
from openai import OpenAI

class EthicsO3Solver:
    def __init__(self, api_key: str):
        self.client = OpenAI(api_key=api_key)
        self.model = "o3"
        
        # Ethics-specific settings
        self.max_iterations = 3
        self.max_completion_tokens = 800  # Slightly higher for complex ethics proofs
        
        # Statistics
        self.stats = {
            'total_sorries': 0,
            'resolved_sorries': 0,
            'llm_calls': 0,
            'compile_successes': 0,
            'compile_failures': 0
        }
        
        # Ethics-specific patterns
        self.ethics_patterns = {
            'floor_arithmetic': {
                'indicators': ['Int.floor', 'floor', '⌊', '⌋'],
                'tactics': ['interval_cases', 'omega', 'decide', 'by_cases'],
                'difficulty': 'hard'
            },
            'virtue_propagation': {
                'indicators': ['PropagateVirtues', 'TrainVirtue', 'virtue'],
                'tactics': ['simp [PropagateVirtues]', 'unfold TrainVirtue', 'apply virtue_reduces_curvature'],
                'difficulty': 'medium'
            },
            'curvature_bounds': {
                'indicators': ['κ', 'curvature', 'balance'],
                'tactics': ['apply BoundedState.lower_bound', 'apply BoundedState.upper_bound', 'linarith'],
                'difficulty': 'medium'
            },
            'list_operations': {
                'indicators': ['List.map', 'List.sum', 'List.filter'],
                'tactics': ['simp', 'induction', 'apply List.sum_lt_sum'],
                'difficulty': 'hard'
            },
            'philosophical': {
                'indicators': ['consciousness', 'meta-ethical', '45-gap'],
                'tactics': ['sorry -- Philosophical claim beyond formalization'],
                'difficulty': 'skip'
            }
        }
        
        # Successful ethics examples
        self.ethics_examples = [
            {
                'theorem': 'fusion_reduces_uncertainty',
                'pattern': 'harmonic mean calculation',
                'proof': '''by
  simp [fuseMeasurements]
  have h_calc : 1 / (1/2.5 + 1/4.0 + 1/8.0) = 1 / (0.4 + 0.25 + 0.125) := by norm_num
  rw [h_calc]
  norm_num'''
            },
            {
                'theorem': 'virtue_training_effectiveness',
                'pattern': 'non-zero curvature requirement',
                'proof': '''by
  intro students curriculum h_nonzero
  let trained := curriculum.foldl (fun acc v => acc.map (TrainVirtue v)) students
  use trained
  constructor
  · simp [trained]
  · cases curriculum with
    | nil => simp [trained]; exact h_nonzero
    | cons v vs => 
      apply virtue_reduces_systemic_curvature
      exact h_nonzero'''
            }
        ]
        
        # Create backup directory
        self.backup_dir = None
        
    def create_backup(self):
        """Create timestamped backup of ethics module"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir = Path(f"backups/ethics_{timestamp}")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        # Backup ethics files
        ethics_dir = Path("ethics")
        if ethics_dir.exists():
            for file in ethics_dir.glob("*.lean"):
                shutil.copy2(file, self.backup_dir / file.name)
        
        print(f"Created backup at {self.backup_dir}")
        
    def classify_sorry(self, sorry_info):
        """Classify sorry by pattern to determine approach"""
        declaration = sorry_info['declaration']
        
        for pattern_name, pattern in self.ethics_patterns.items():
            if any(indicator in declaration for indicator in pattern['indicators']):
                return pattern_name, pattern
                
        return 'general', {'tactics': ['simp', 'norm_num', 'linarith'], 'difficulty': 'medium'}
        
    def build_ethics_context(self, file_path: Path, sorry_info):
        """Build ethics-specific context"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        context = {
            'imports': [],
            'instances': [],
            'definitions': [],
            'related_theorems': []
        }
        
        # Get imports
        for line in lines[:30]:
            if line.strip().startswith('import'):
                context['imports'].append(line.strip())
                
        # Find instances (BoundedState, CurvatureMetric, etc.)
        for i, line in enumerate(lines):
            if 'instance' in line:
                instance_lines = [line]
                j = i + 1
                while j < len(lines) and not lines[j].strip().startswith(('theorem', 'lemma', 'def', 'instance')):
                    instance_lines.append(lines[j])
                    j += 1
                context['instances'].append(''.join(instance_lines))
                
        # Get key definitions used in this theorem
        pattern_name, _ = self.classify_sorry(sorry_info)
        if pattern_name == 'virtue_propagation':
            # Find virtue-related definitions
            for i, line in enumerate(lines):
                if any(d in line for d in ['def PropagateVirtues', 'def TrainVirtue', 'def Virtue']):
                    def_lines = self.extract_definition(lines, i)
                    context['definitions'].append(def_lines)
                    
        elif pattern_name == 'curvature_bounds':
            # Find curvature-related definitions
            for i, line in enumerate(lines):
                if any(d in line for d in ['def κ', 'def curvature', 'class BoundedState']):
                    def_lines = self.extract_definition(lines, i)
                    context['definitions'].append(def_lines)
                    
        return context
        
    def extract_definition(self, lines, start_idx):
        """Extract a complete definition from lines"""
        def_lines = []
        i = start_idx
        indent = len(lines[i]) - len(lines[i].lstrip())
        
        while i < len(lines):
            if i > start_idx and lines[i].strip() and len(lines[i]) - len(lines[i].lstrip()) <= indent:
                # Found next definition at same or lower indent
                break
            def_lines.append(lines[i])
            i += 1
            
        return ''.join(def_lines)
        
    def generate_ethics_proof(self, sorry_info, context, pattern_info, previous_error=None):
        """Generate proof specifically for ethics module"""
        
        pattern_name, pattern = pattern_info
        
        # Skip philosophical sorries
        if pattern['difficulty'] == 'skip':
            return None
            
        prompt = f"""You are an expert Lean 4 theorem prover working on a machine-verifiable ethics module.

## CONTEXT

### Module Overview:
This ethics module formalizes moral states, virtue cultivation, and curvature-based ethics.
Key concepts:
- MoralState with energy fields and ledger balances
- Curvature κ measures deviation from ethical ideal (0 is perfect)
- Virtues reduce curvature through training and propagation
- Floor operations create discrete challenges

### Available Imports:
{chr(10).join(context['imports'][:5])}

### Key Instances:
{chr(10).join(context['instances'][:2])}

### Relevant Definitions:
{chr(10).join(context['definitions'][:3])}

### Pattern Classification: {pattern_name}
Expected tactics: {', '.join(pattern['tactics'][:5])}

### Similar Successful Proofs:
"""
        
        # Add relevant examples
        for ex in self.ethics_examples:
            if pattern_name in ex.get('pattern', ''):
                prompt += f"\n{ex['theorem']}:\n{ex['proof']}\n"
                
        prompt += f"""
### Target Theorem:
{sorry_info['declaration']}

"""

        if previous_error:
            prompt += f"""### Previous Error:
{previous_error}

Focus on fixing this specific error.
"""

        prompt += """## YOUR TASK

Provide a Lean 4 proof that:
1. Handles discrete operations (floor, ceiling) carefully
2. Uses available instances (BoundedState, etc.)
3. Follows the style of successful ethics proofs
4. Is concise and compiles correctly

IMPORTANT NOTES:
- Floor operations often break continuous properties
- Use interval_cases or omega for discrete arithmetic
- Check bounds using BoundedState instances
- For lists, use induction or library lemmas

Output ONLY the Lean proof code.
"""

        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[
                    {"role": "system", "content": "You are a Lean 4 expert. Output only valid Lean code."},
                    {"role": "user", "content": prompt}
                ],
                max_completion_tokens=self.max_completion_tokens
            )
            
            proof = response.choices[0].message.content.strip()
            self.stats['llm_calls'] += 1
            
            # Clean up
            if '```' in proof:
                match = re.search(r'```(?:lean)?\s*\n(.*?)\n```', proof, re.DOTALL)
                if match:
                    proof = match.group(1)
                    
            return proof.strip()
            
        except Exception as e:
            print(f"  Error calling o3: {e}")
            return None
            
    def validate_and_apply_proof(self, file_path: Path, sorry_info, proof):
        """Validate proof and apply if successful"""
        
        # Create temp backup
        temp_backup = str(file_path) + '.temp'
        shutil.copy2(file_path, temp_backup)
        
        try:
            # Read file
            with open(file_path, 'r') as f:
                content = f.read()
                lines = content.split('\n')
                
            # Replace sorry
            sorry_line = lines[sorry_info['line'] - 1]
            if 'by sorry' in sorry_line:
                new_line = sorry_line.replace('by sorry', proof)
            elif ':= sorry' in sorry_line:
                new_line = sorry_line.replace('sorry', proof)
            else:
                new_line = sorry_line.replace('sorry', proof)
                
            lines[sorry_info['line'] - 1] = new_line
            
            # Write modified content
            with open(file_path, 'w') as f:
                f.write('\n'.join(lines))
                
            # Test compilation
            result = subprocess.run(
                ['lake', 'build', str(file_path)],
                capture_output=True,
                text=True,
                timeout=60,
                cwd=file_path.parent.parent  # Run from project root
            )
            
            if result.returncode == 0:
                # Success!
                os.remove(temp_backup)
                self.stats['compile_successes'] += 1
                self.stats['resolved_sorries'] += 1
                print(f"  ✓ Proof successful!")
                return True, None
            else:
                # Failed - restore
                shutil.copy2(temp_backup, file_path)
                os.remove(temp_backup)
                self.stats['compile_failures'] += 1
                
                # Extract error
                error = self.extract_first_error(result.stderr or result.stdout)
                print(f"  ✗ Compilation failed: {error}")
                return False, error
                
        except Exception as e:
            # Restore on any error
            if os.path.exists(temp_backup):
                shutil.copy2(temp_backup, file_path)
                os.remove(temp_backup)
            print(f"  ✗ Error: {e}")
            return False, str(e)
            
    def extract_first_error(self, error_msg: str):
        """Extract first meaningful error"""
        for line in error_msg.split('\n'):
            if 'error:' in line.lower():
                return line[:200]
        return error_msg[:200] if error_msg else "Unknown error"
        
    def find_sorries(self, file_path: Path):
        """Find all sorries in a file"""
        sorries = []
        
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Find theorem declaration
                for j in range(i, -1, -1):
                    if any(kw in lines[j] for kw in ['theorem ', 'lemma ']):
                        # Extract declaration
                        decl_lines = []
                        k = j
                        while k <= i:
                            decl_lines.append(lines[k])
                            k += 1
                            
                        # Extract name
                        match = re.search(r'(?:theorem|lemma)\s+(\w+)', lines[j])
                        if match:
                            sorries.append({
                                'line': i + 1,
                                'name': match.group(1),
                                'declaration': ''.join(decl_lines).strip()
                            })
                        break
                        
        return sorries
        
    def solve_file(self, file_path: Path):
        """Solve all sorries in a file"""
        print(f"\n{'='*60}")
        print(f"Processing: {file_path}")
        print('='*60)
        
        sorries = self.find_sorries(file_path)
        if not sorries:
            print("No sorries found!")
            return
            
        print(f"Found {len(sorries)} sorries")
        self.stats['total_sorries'] += len(sorries)
        
        for sorry_info in sorries:
            print(f"\n--- {sorry_info['name']} (line {sorry_info['line']}) ---")
            
            # Classify sorry
            pattern_info = self.classify_sorry(sorry_info)
            pattern_name, pattern = pattern_info
            print(f"Pattern: {pattern_name} (difficulty: {pattern['difficulty']})")
            
            if pattern['difficulty'] == 'skip':
                print("  ⚠️  Skipping philosophical sorry")
                continue
                
            # Build context
            context = self.build_ethics_context(file_path, sorry_info)
            
            # Try multiple iterations
            best_error = None
            for iteration in range(self.max_iterations):
                print(f"  Attempt {iteration + 1}/{self.max_iterations}...")
                
                # Generate proof
                proof = self.generate_ethics_proof(sorry_info, context, pattern_info, best_error)
                
                if not proof:
                    continue
                    
                print(f"  Generated: {proof[:80]}...")
                
                # Validate and apply
                success, error = self.validate_and_apply_proof(file_path, sorry_info, proof)
                
                if success:
                    break
                else:
                    best_error = error
                    
    def run_campaign(self):
        """Run the ethics module campaign"""
        print("\n" + "="*60)
        print("ETHICS MODULE O3 SOLVER")
        print("="*60)
        print("Features:")
        print("- Pattern-based classification")
        print("- Ethics-specific context building")
        print("- Floor arithmetic handling")
        print("- Philosophical sorry detection")
        print("-" * 60)
        
        # Create backup
        self.create_backup()
        
        # Target files in order of complexity
        ethics_files = [
            Path("ethics/Measurement.lean"),
            Path("ethics/EmpiricalData.lean"),
            Path("ethics/Applications.lean"),
            Path("ethics/Virtue.lean"),
            Path("ethics/Main.lean"),
        ]
        
        for file_path in ethics_files:
            if file_path.exists():
                self.solve_file(file_path)
                
        # Report statistics
        print(f"\n{'='*60}")
        print("FINAL STATISTICS")
        print('='*60)
        print(f"Total sorries found: {self.stats['total_sorries']}")
        print(f"Sorries resolved: {self.stats['resolved_sorries']}")
        print(f"Success rate: {self.stats['resolved_sorries'] / max(1, self.stats['total_sorries']):.1%}")
        print(f"LLM calls: {self.stats['llm_calls']}")
        print(f"Compile successes: {self.stats['compile_successes']}")
        print(f"Compile failures: {self.stats['compile_failures']}")
        print(f"\nBackup saved at: {self.backup_dir}")

def main():
    # Get API key
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("Error: Please set OPENAI_API_KEY environment variable")
        print("export OPENAI_API_KEY='sk-proj-...'")
        return
        
    solver = EthicsO3Solver(api_key)
    solver.run_campaign()

if __name__ == "__main__":
    main() 