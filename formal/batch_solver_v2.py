#!/usr/bin/env python3
"""
Recognition Science Batch Solver v2
Targets 25+ high-probability theorems with proven patterns
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
class ProofTarget:
    name: str
    file: str
    pattern: str
    expected_proof: str
    priority: int  # 1=highest, 5=lowest

class BatchSolverV2:
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
        
        # High-probability targets based on scan results
        self.targets = [
            # Priority 1: Already working patterns
            ProofTarget("E_coh_pos", "formal/TestSolver.lean", "unfold+norm_num", "unfold E_coh\nnorm_num", 1),
            
            # Priority 2: Simple arithmetic (norm_num pattern)
            ProofTarget("gradeNat_one", "formal/Pattern/PrimeCorrespondence.lean", "norm_num", "norm_num", 2),
            ProofTarget("tick_one", "formal/Pattern/EightBeat.lean", "norm_num", "norm_num", 2),
            ProofTarget("grade_one", "formal/Pattern/FreeRecognition.lean", "norm_num", "norm_num", 2),
            ProofTarget("length_one", "formal/Pattern/FreeRecognition.lean", "norm_num", "norm_num", 2),
            ProofTarget("eight_from_lcm", "formal/MetaPrinciple.lean", "norm_num", "norm_num", 2),
            ProofTarget("eight_beat_lcm", "formal/CompletelyRigorous.lean", "norm_num", "norm_num", 2),
            ProofTarget("J_one", "formal/CompletelyRigorous.lean", "unfold+norm_num", "unfold J\nnorm_num", 2),
            
            # Priority 3: Positivity theorems (unfold+norm_num pattern)
            ProofTarget("tau_pos", "formal/SimpleWorkingProof.lean", "unfold+norm_num", "unfold τ₀\nnorm_num", 3),
            ProofTarget("eight_beat_pos", "formal/SimpleWorkingProof.lean", "unfold+norm_num", "unfold eight_beat_period\nnorm_num", 3),
            ProofTarget("coherence_positive", "formal/SimpleDemo.lean", "unfold+norm_num", "unfold coherence_quantum\nnorm_num", 3),
            
            # Priority 4: Definitional equality (rfl pattern)
            ProofTarget("electron_at_rung_zero", "formal/SimpleWorkingProof.lean", "rfl", "rfl", 4),
            ProofTarget("mass_at_rung_one", "formal/SimpleWorkingProof.lean", "unfold+rfl", "unfold mass_at_rung\nrfl", 4),
            ProofTarget("electron_mass_is_E_coh", "formal/GoldenRatioDemo.lean", "rfl", "rfl", 4),
            
            # Priority 5: More complex but still tractable
            ProofTarget("phi_times_two", "formal/SimpleWorkingProof.lean", "unfold+ring", "unfold φ\nring", 5),
            ProofTarget("phi_minus_one_pos", "formal/SimpleWorkingProof.lean", "unfold+norm_num", "unfold φ\nnorm_num", 5),
        ]

    def extract_theorem_info(self, file_path: str, theorem_name: str) -> Optional[dict]:
        """Extract theorem information from file"""
        try:
            if not os.path.exists(file_path):
                logging.error(f"File not found: {file_path}")
                return None
                
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Find the theorem with sorry
            pattern = rf'(theorem|lemma)\s+{re.escape(theorem_name)}\s*[^:]*:[^:=]*:=\s*by\s*sorry[^\n]*'
            match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
            
            if not match:
                logging.error(f"Theorem {theorem_name} not found or already completed")
                return None
                
            return {
                'theorem_text': match.group(0),
                'content': content,
                'match': match
            }
            
        except Exception as e:
            logging.error(f"Error extracting {theorem_name} from {file_path}: {e}")
            return None

    def generate_proof(self, target: ProofTarget, theorem_info: dict) -> Optional[str]:
        """Generate proof using Claude with specific pattern guidance"""
        
        prompt = f"""You are proving a theorem in Recognition Science using Lean 4.

THEOREM: {target.name}
PATTERN: {target.pattern}
EXPECTED: {target.expected_proof}

CONTEXT:
{theorem_info['theorem_text']}

RECOGNITION SCIENCE CONSTANTS:
- φ = (1 + √5)/2 (golden ratio)
- E_coh : ℝ := 0.090 (coherence quantum)
- τ₀ : ℝ := 7.33e-15 (minimal tick)
- eight_beat_period = 8 * τ₀

PROVEN WORKING PATTERNS:
1. norm_num - for arithmetic like 2+2=4, lcm calculations
2. unfold X; norm_num - for constants > 0 like E_coh > 0
3. rfl - for definitional equality
4. unfold X; rfl - for definitions that need unfolding

CRITICAL: Provide ONLY the tactics to replace 'sorry'.
- No 'by' prefix
- No explanations
- Use the expected pattern as template
- Keep it minimal (1-2 lines max)

Expected output format examples:
- "norm_num"
- "unfold E_coh\\nnorm_num"
- "rfl"
"""

        try:
            response = self.client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=50,  # Keep it very short
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up the proof
            if proof.startswith('```'):
                proof = re.sub(r'^```\w*\n', '', proof)
                proof = re.sub(r'\n```$', '', proof)
            proof = proof.strip()
            
            # Remove explanatory text, keep only tactics
            lines = proof.split('\n')
            clean_lines = []
            for line in lines:
                line = line.strip()
                if line and not line.startswith('--') and not line.startswith('//'):
                    # Only keep lines with valid tactics
                    if any(tactic in line for tactic in ['norm_num', 'unfold', 'rfl', 'ring', 'simp', 'positivity']):
                        clean_lines.append(line)
            
            proof = '\n'.join(clean_lines)
            
            if proof and len(proof) > 1:
                return 'by ' + proof
            else:
                logging.error(f"Generated proof too short: '{proof}'")
                return None
                
        except Exception as e:
            logging.error(f"Error generating proof: {e}")
            return None

    def verify_and_apply_proof(self, target: ProofTarget, theorem_info: dict, proof: str) -> bool:
        """Verify proof compiles and apply if successful"""
        try:
            # Replace the sorry with our proof
            pattern = rf'(theorem|lemma)\s+{re.escape(target.name)}\s*[^:]*:[^:=]*:=\s*by\s*sorry[^\n]*'
            replacement = lambda m: re.sub(r'by\s*sorry[^\n]*', proof, m.group(0))
            
            modified_content = re.sub(pattern, replacement, theorem_info['content'], flags=re.MULTILINE | re.DOTALL)
            
            if modified_content == theorem_info['content']:
                logging.error(f"Failed to replace sorry in {target.name}")
                return False
            
            # Write temporary file
            temp_file = target.file + '.temp'
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
                with open(target.file, 'w') as f:
                    f.write(modified_content)
                logging.info(f"✅ {target.name} - PROOF APPLIED!")
                return True
            else:
                logging.error(f"❌ {target.name} - Compilation failed: {result.stderr[:100]}")
                return False
                
        except Exception as e:
            logging.error(f"Error verifying {target.name}: {e}")
            return False

    def run(self):
        """Run the batch solver"""
        print("\n🚀 Recognition Science Batch Solver v2")
        print("=" * 50)
        print(f"Targeting {len(self.targets)} high-probability theorems")
        print("Using proven patterns: norm_num, unfold+norm_num, rfl")
        
        start_time = time.time()
        
        # Sort by priority
        sorted_targets = sorted(self.targets, key=lambda x: x.priority)
        
        for i, target in enumerate(sorted_targets, 1):
            print(f"\n[{i}/{len(self.targets)}] {target.name} (Priority {target.priority}, {target.pattern})")
            
            # Extract theorem info
            theorem_info = self.extract_theorem_info(target.file, target.name)
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
                    'priority': target.priority
                })
                print(f"🎉 SUCCESS: {target.name}")
            else:
                self.results['failed'] += 1
                self.results['failed_theorems'].append(target.name)
        
        # Save results
        self.results['time_minutes'] = (time.time() - start_time) / 60
        
        with open('batch_solver_v2_results.json', 'w') as f:
            json.dump(self.results, f, indent=2)
        
        # Summary
        print(f"\n🎯 BATCH SOLVER V2 COMPLETE")
        print(f"✅ Completed: {self.results['completed']}/{self.results['total_attempted']}")
        print(f"⏱️  Time: {self.results['time_minutes']:.1f} minutes")
        print(f"📈 Success Rate: {self.results['completed']/max(1,self.results['total_attempted'])*100:.1f}%")
        
        if self.results['completed_theorems']:
            print(f"\n🎉 Successfully completed:")
            for theorem in self.results['completed_theorems']:
                print(f"   - {theorem['name']} ({theorem['pattern']}, P{theorem['priority']})")
        
        if self.results['failed_theorems']:
            print(f"\n❌ Failed theorems:")
            for name in self.results['failed_theorems']:
                print(f"   - {name}")

if __name__ == "__main__":
    solver = BatchSolverV2()
    solver.run() 