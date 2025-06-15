#!/usr/bin/env python3
"""
Focused Recognition Science Proof Solver
Targets specific theorems with proven successful patterns
"""

import os
import re
import json
import logging
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional
import subprocess
import time
from datetime import datetime

import anthropic

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

@dataclass
class ProofTask:
    theorem_name: str
    file_path: str
    theorem_statement: str
    context: str
    imports: List[str]
    proof: Optional[str] = None
    success: bool = False

class FocusedSolver:
    def __init__(self):
        self.client = anthropic.Anthropic(api_key=os.getenv('ANTHROPIC_API_KEY'))
        self.results = {
            'timestamp': datetime.now().isoformat(),
            'completed_theorems': [],
            'failed_theorems': [],
            'total_attempted': 0,
            'completed': 0,
            'verified': 0,
            'failed': 0
        }
        
        # Specific theorems we know should work based on patterns
        self.target_theorems = [
            # Pattern: positivity (for golden ratio)
            {
                'name': 'phi_pos', 
                'file': 'formal/Core/GoldenRatio.lean',
                'pattern': 'positivity',
                'expected': 'positivity'
            },
            # Pattern: unfold + ring (for golden ratio equation)
            {
                'name': 'phi_equation',
                'file': 'formal/Core/GoldenRatio.lean', 
                'pattern': 'unfold + ring',
                'expected': 'unfold φ\nring'
            },
            # Pattern: positivity (for phi > 1)
            {
                'name': 'phi_gt_one',
                'file': 'formal/Core/GoldenRatio.lean',
                'pattern': 'positivity',
                'expected': 'positivity'
            },
            # Pattern: linarith (for J_ge_one)
            {
                'name': 'J_ge_one',
                'file': 'formal/Core/GoldenRatio.lean',
                'pattern': 'linarith',
                'expected': 'unfold J\nlinarith'
            }
        ]

    def extract_theorem_info(self, file_path: str, theorem_name: str) -> Optional[ProofTask]:
        """Extract theorem information from file"""
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Find the theorem
            pattern = rf'(theorem|lemma)\s+{re.escape(theorem_name)}\s*[^:]*:[^:=]*:=\s*by\s*sorry[^\n]*'
            match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
            
            if not match:
                return None
                
            theorem_text = match.group(0)
            
            # Extract imports
            imports = re.findall(r'^import\s+(.+)$', content, re.MULTILINE)
            
            # Get context around theorem
            start = max(0, match.start() - 500)
            end = min(len(content), match.end() + 500)
            context = content[start:end]
            
            return ProofTask(
                theorem_name=theorem_name,
                file_path=file_path,
                theorem_statement=theorem_text,
                context=context,
                imports=imports
            )
            
        except Exception as e:
            logging.error(f"Error extracting {theorem_name} from {file_path}: {e}")
            return None

    def generate_proof(self, task: ProofTask, expected_pattern: str) -> bool:
        """Generate proof using Claude with specific pattern guidance"""
        
        prompt = f"""You are proving a theorem in Recognition Science using Lean 4.

THEOREM: {task.theorem_name}
{task.theorem_statement}

EXPECTED PATTERN: {expected_pattern}

RECOGNITION SCIENCE DEFINITIONS:
- φ = (1 + √5)/2 (golden ratio)
- E_coh : ℝ := 0.090 (coherence quantum in eV)
- τ₀ : ℝ := 7.33e-15 (minimal tick in seconds)
- J(x) = (x + 1/x)/2 (cost functional)

PROVEN SUCCESSFUL PATTERNS:
1. For constants > 0: "unfold <name>\\nnorm_num"
2. For φ > 0: "positivity" 
3. For φ² = φ + 1: "unfold φ\\nring"
4. For definitions: "rfl"

CRITICAL: Provide ONLY the tactics (no 'by', no explanations).
Use the expected pattern as guidance.
Keep it minimal - usually 1-2 lines maximum.

Example outputs:
- "norm_num"
- "positivity" 
- "unfold E_coh\\nnorm_num"
- "rfl"
"""

        try:
            response = self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=100,  # Keep it short
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up the proof
            if proof.startswith('```'):
                proof = re.sub(r'^```\w*\n', '', proof)
                proof = re.sub(r'\n```$', '', proof)
            proof = proof.strip()
            
            # Remove any explanatory text
            lines = proof.split('\n')
            clean_lines = []
            for line in lines:
                line = line.strip()
                if line and not line.startswith('--') and not line.startswith('//'):
                    # Only keep lines that look like tactics
                    if any(tactic in line for tactic in ['norm_num', 'positivity', 'unfold', 'rfl', 'ring', 'simp']):
                        clean_lines.append(line)
            
            proof = '\n'.join(clean_lines)
            
            if proof and len(proof) > 2:
                task.proof = 'by ' + proof
                logging.info(f"   Generated: {task.proof}")
                return True
            else:
                logging.error(f"   Generated proof too short: '{proof}'")
                return False
                
        except Exception as e:
            logging.error(f"   Error generating proof: {e}")
            return False

    def verify_proof(self, task: ProofTask) -> bool:
        """Verify proof compiles"""
        try:
            # Read original file
            with open(task.file_path, 'r') as f:
                original_content = f.read()
            
            # Replace the sorry with our proof
            pattern = rf'(theorem|lemma)\s+{re.escape(task.theorem_name)}\s*[^:]*:[^:=]*:=\s*by\s*sorry[^\n]*'
            replacement = lambda m: re.sub(r'by\s*sorry[^\n]*', task.proof, m.group(0))
            
            modified_content = re.sub(pattern, replacement, original_content, flags=re.MULTILINE | re.DOTALL)
            
            if modified_content == original_content:
                logging.error(f"   Failed to replace sorry in {task.theorem_name}")
                return False
            
            # Write temporary file
            temp_file = task.file_path + '.temp'
            with open(temp_file, 'w') as f:
                f.write(modified_content)
            
            # Test compilation
            result = subprocess.run(
                ['lake', 'env', 'lean', temp_file],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # Clean up temp file
            os.remove(temp_file)
            
            if result.returncode == 0:
                # Apply the change permanently
                with open(task.file_path, 'w') as f:
                    f.write(modified_content)
                logging.info(f"   ✅ Proof verified and applied!")
                return True
            else:
                logging.error(f"   ❌ Proof failed: {result.stderr[:200]}")
                return False
                
        except Exception as e:
            logging.error(f"   Error verifying proof: {e}")
            return False

    def run(self):
        """Run the focused solver"""
        print("\n🎯 Focused Recognition Science Proof Solver")
        print("=" * 50)
        print(f"Targeting {len(self.target_theorems)} specific theorems with proven patterns")
        
        start_time = time.time()
        
        for i, target in enumerate(self.target_theorems, 1):
            print(f"\n[{i}/{len(self.target_theorems)}] {target['name']} ({target['pattern']})")
            
            # Extract theorem info
            task = self.extract_theorem_info(target['file'], target['name'])
            if not task:
                logging.error(f"   Could not find theorem {target['name']}")
                self.results['failed'] += 1
                continue
            
            self.results['total_attempted'] += 1
            
            # Generate proof
            if not self.generate_proof(task, target['expected']):
                self.results['failed'] += 1
                self.results['failed_theorems'].append(target['name'])
                continue
            
            # Verify proof
            if self.verify_proof(task):
                self.results['completed'] += 1
                self.results['verified'] += 1
                self.results['completed_theorems'].append({
                    'name': target['name'],
                    'file': target['file'],
                    'proof': task.proof,
                    'pattern': target['pattern']
                })
                print(f"   🎉 SUCCESS: {target['name']}")
            else:
                self.results['failed'] += 1
                self.results['failed_theorems'].append(target['name'])
        
        # Save results
        self.results['time_minutes'] = (time.time() - start_time) / 60
        
        with open('focused_solver_results.json', 'w') as f:
            json.dump(self.results, f, indent=2)
        
        # Summary
        print(f"\n🎯 FOCUSED SOLVER COMPLETE")
        print(f"   ✅ Completed: {self.results['completed']}/{self.results['total_attempted']}")
        print(f"   ⏱️  Time: {self.results['time_minutes']:.1f} minutes")
        
        if self.results['completed_theorems']:
            print(f"\n🎉 Successfully completed:")
            for theorem in self.results['completed_theorems']:
                print(f"   - {theorem['name']} ({theorem['pattern']})")

if __name__ == "__main__":
    solver = FocusedSolver()
    solver.run() 