#!/usr/bin/env python3
"""
Recognition Science Real Batch Solver
Targets actual theorems with sorry found in the codebase
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
class RealTarget:
    name: str
    file: str
    pattern: str
    expected_proof: str
    difficulty: int  # 1=easy, 5=hard

class RealBatchSolver:
    def __init__(self):
        self.client = anthropic.Anthropic(api_key=os.getenv('ANTHROPIC_API_KEY'))
        self.results = {
            'timestamp': datetime.now().isoformat(),
            'completed_theorems': [],
            'failed_theorems': [],
            'total_attempted': 0,
            'completed': 0,
            'verified': 0,
            'failed': 0,
            'time_minutes': 0
        }
        
        # Real targets found in the codebase with sorry
        self.targets = [
            # From Core/GoldenRatio.lean - these should be easier
            RealTarget("J_ge_one", "formal/Core/GoldenRatio.lean", "linarith", "unfold J\nlinarith", 2),
            RealTarget("phi_pos", "formal/Core/GoldenRatio.lean", "positivity", "positivity", 2),
            RealTarget("phi_gt_one", "formal/Core/GoldenRatio.lean", "positivity", "positivity", 2),
            RealTarget("phi_equation", "formal/Core/GoldenRatio.lean", "ring", "unfold φ\nring", 3),
            
            # From Core/CostFunctional.lean - more challenging
            RealTarget("cost_zero_iff_empty", "formal/Core/CostFunctional.lean", "simp", "simp [ledger_cost]", 4),
            RealTarget("J_strict_convex", "formal/Core/CostFunctional.lean", "calculus", "sorry -- Too complex for now", 5),
        ]

    def scan_for_theorems(self, file_path: str) -> List[str]:
        """Scan file for theorem names with sorry"""
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Find all theorems with sorry
            pattern = r'theorem\s+(\w+)[^:]*:[^:=]*:=\s*by\s*sorry'
            matches = re.findall(pattern, content, re.MULTILINE | re.DOTALL)
            return matches
            
        except Exception as e:
            logging.error(f"Error scanning {file_path}: {e}")
            return []

    def extract_theorem_context(self, file_path: str, theorem_name: str) -> Optional[dict]:
        """Extract full theorem context"""
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Find the theorem with more context
            pattern = rf'theorem\s+{re.escape(theorem_name)}\s*[^:]*:[^:=]*:=\s*by\s*sorry[^\n]*'
            match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
            
            if not match:
                return None
                
            # Get surrounding context
            start = max(0, match.start() - 300)
            end = min(len(content), match.end() + 300)
            context = content[start:end]
            
            return {
                'theorem_text': match.group(0),
                'context': context,
                'content': content,
                'match': match
            }
            
        except Exception as e:
            logging.error(f"Error extracting {theorem_name}: {e}")
            return None

    def generate_proof(self, target: RealTarget, theorem_info: dict) -> Optional[str]:
        """Generate proof with enhanced context"""
        
        prompt = f"""You are proving a theorem in Recognition Science using Lean 4.

THEOREM: {target.name}
DIFFICULTY: {target.difficulty}/5
EXPECTED PATTERN: {target.pattern}

THEOREM STATEMENT:
{theorem_info['theorem_text']}

SURROUNDING CONTEXT:
{theorem_info['context']}

RECOGNITION SCIENCE DEFINITIONS:
- φ = (1 + √5)/2 (golden ratio)
- J(x) = (x + 1/x)/2 (cost functional)
- E_coh = 0.090 eV (coherence quantum)

PROVEN TACTICS THAT WORK:
1. norm_num - for numerical calculations
2. unfold X; norm_num - for constants > 0
3. positivity - for proving > 0 (needs proper imports)
4. linarith - for linear arithmetic
5. ring - for ring operations
6. simp - for simplification
7. rfl - for definitional equality

CRITICAL INSTRUCTIONS:
- Provide ONLY the tactics (no 'by' prefix)
- Keep it simple (1-3 tactics maximum)
- For J_ge_one: try "unfold J; linarith" or "unfold J; norm_num"
- For phi_pos/phi_gt_one: try "positivity" or "norm_num"
- For phi_equation: try "unfold φ; ring" or "unfold φ; field_simp; ring"

Output only the tactics, nothing else."""

        try:
            response = self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=100,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up
            if proof.startswith('```'):
                proof = re.sub(r'^```\w*\n', '', proof)
                proof = re.sub(r'\n```$', '', proof)
            proof = proof.strip()
            
            # Extract only tactic lines
            lines = proof.split('\n')
            clean_lines = []
            for line in lines:
                line = line.strip()
                if line and not line.startswith('--') and not line.startswith('//'):
                    if any(tactic in line for tactic in ['norm_num', 'unfold', 'positivity', 'linarith', 'ring', 'simp', 'rfl', 'field_simp']):
                        clean_lines.append(line)
            
            proof = '\n'.join(clean_lines)
            
            if proof and len(proof) > 1:
                return 'by ' + proof
            else:
                return None
                
        except Exception as e:
            logging.error(f"Error generating proof: {e}")
            return None

    def verify_and_apply_proof(self, target: RealTarget, theorem_info: dict, proof: str) -> bool:
        """Verify and apply proof"""
        try:
            # Replace sorry with proof
            pattern = rf'theorem\s+{re.escape(target.name)}\s*[^:]*:[^:=]*:=\s*by\s*sorry[^\n]*'
            replacement = lambda m: re.sub(r'by\s*sorry[^\n]*', proof, m.group(0))
            
            modified_content = re.sub(pattern, replacement, theorem_info['content'], flags=re.MULTILINE | re.DOTALL)
            
            if modified_content == theorem_info['content']:
                logging.error(f"Failed to replace sorry in {target.name}")
                return False
            
            # Test with temporary file
            temp_file = target.file + '.temp'
            with open(temp_file, 'w') as f:
                f.write(modified_content)
            
            result = subprocess.run(
                ['lake', 'env', 'lean', temp_file],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            os.remove(temp_file)
            
            if result.returncode == 0:
                # Apply permanently
                with open(target.file, 'w') as f:
                    f.write(modified_content)
                return True
            else:
                logging.error(f"Compilation failed: {result.stderr[:150]}")
                return False
                
        except Exception as e:
            logging.error(f"Error verifying {target.name}: {e}")
            return False

    def run(self):
        """Run the real batch solver"""
        print("\n🎯 Recognition Science REAL Batch Solver")
        print("=" * 50)
        print("Targeting actual theorems with sorry found in codebase")
        
        # First, scan for additional theorems
        print("\n🔍 Scanning for theorems with sorry...")
        for target in self.targets:
            if os.path.exists(target.file):
                found_theorems = self.scan_for_theorems(target.file)
                print(f"   {target.file}: {found_theorems}")
        
        start_time = time.time()
        
        # Sort by difficulty (easiest first)
        sorted_targets = sorted(self.targets, key=lambda x: x.difficulty)
        
        for i, target in enumerate(sorted_targets, 1):
            print(f"\n[{i}/{len(self.targets)}] {target.name} (Difficulty {target.difficulty}/5)")
            
            # Extract theorem
            theorem_info = self.extract_theorem_context(target.file, target.name)
            if not theorem_info:
                self.results['failed'] += 1
                self.results['failed_theorems'].append(target.name)
                continue
            
            self.results['total_attempted'] += 1
            
            # Generate proof
            proof = self.generate_proof(target, theorem_info)
            if not proof:
                self.results['failed'] += 1
                self.results['failed_theorems'].append(target.name)
                continue
            
            logging.info(f"Generated: {proof}")
            
            # Verify and apply
            if self.verify_and_apply_proof(target, theorem_info, proof):
                self.results['completed'] += 1
                self.results['verified'] += 1
                self.results['completed_theorems'].append({
                    'name': target.name,
                    'file': target.file,
                    'proof': proof,
                    'pattern': target.pattern,
                    'difficulty': target.difficulty
                })
                print(f"🎉 SUCCESS: {target.name}")
            else:
                self.results['failed'] += 1
                self.results['failed_theorems'].append(target.name)
        
        # Save results
        self.results['time_minutes'] = (time.time() - start_time) / 60
        
        with open('real_batch_solver_results.json', 'w') as f:
            json.dump(self.results, f, indent=2)
        
        # Summary
        print(f"\n🎯 REAL BATCH SOLVER COMPLETE")
        print(f"✅ Completed: {self.results['completed']}/{self.results['total_attempted']}")
        print(f"⏱️  Time: {self.results['time_minutes']:.1f} minutes")
        if self.results['total_attempted'] > 0:
            print(f"📈 Success Rate: {self.results['completed']/self.results['total_attempted']*100:.1f}%")
        
        if self.results['completed_theorems']:
            print(f"\n🎉 Successfully completed:")
            for theorem in self.results['completed_theorems']:
                print(f"   - {theorem['name']} (Difficulty {theorem['difficulty']}/5)")

if __name__ == "__main__":
    solver = RealBatchSolver()
    solver.run() 