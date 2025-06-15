#!/usr/bin/env python3
"""
Improved Universe-Level Recognition Science Proof Solver
=======================================================

This version properly handles proof verification and focuses on 
completing proofs that will actually compile.
"""

import os
import re
import json
import time
import subprocess
import logging
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime
import anthropic

# Configuration
API_KEY = os.environ.get("ANTHROPIC_API_KEY")
if not API_KEY:
    raise ValueError("ANTHROPIC_API_KEY environment variable not set")
MODEL = "claude-3-5-sonnet-20241022"

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('solver_run.log'),
        logging.StreamHandler()
    ]
)

@dataclass
class ProofTask:
    file_path: str
    theorem_name: str
    theorem_statement: str
    line_number: int
    context: str
    imports: List[str]
    proof: Optional[str] = None
    success: bool = False
    verified: bool = False
    error_msg: Optional[str] = None

class ImprovedUniverseSolver:
    def __init__(self):
        self.client = anthropic.Anthropic(api_key=API_KEY)
        self.model = MODEL
        self.tasks = []
        self.completed = 0
        self.verified = 0
        self.failed = 0
        
        print("🌌 Improved Universe-Level Recognition Science Proof Solver")
        print("=" * 60)
        print(f"Model: {self.model}")
        print("Mission: Complete the formal framework for reality")
        print()
        
    def scan_priority_files(self):
        """Focus on key files first"""
        print("🔍 Scanning priority theorems...")
        
        # Whitelist of theorems we know should be easy to prove
        whitelist_theorems = [
            # Test theorems (already working)
            "two_plus_two",        # 2 + 2 = 4 - trivial
            "five_gt_three",       # 5 > 3 - trivial
            
            # Basic properties from SimpleWorkingProof
            "E_coh_pos",           # E_coh > 0 - norm_num
            "tau_pos",             # τ₀ > 0 - norm_num  
            "eight_beat_pos",      # eight_beat_period > 0
            "eight_beat_formula",  # eight_beat_period = 8 * τ₀
            "phi_times_two",       # 2 * φ = 1 + sqrt 5
            "phi_minus_one_pos",   # φ - 1 > 0
            "electron_at_rung_zero", # mass_at_rung 0 = E_coh
            "mass_at_rung_one",    # mass_at_rung 1 = E_coh * φ
            
            # Golden ratio theorems (Core/GoldenRatio.lean)
            "phi_pos",             # φ > 0 - basic inequality
            "phi_gt_one",          # φ > 1 - basic inequality
            "J_pos_domain",        # J x = (x + 1/x) / 2 - rfl
            
            # RecognitionScience main file
            "golden_ratio_equation", # φ² = φ + 1 - fundamental
            
            # Basic arithmetic and definitions
            "phi_power",           # Helper function
            "electron_mass_ratio", # Numerical verification
            
            # Cost functional basics
            "J_ge_one",            # J(x) ≥ 1 - AM-GM inequality
            
            # Eight-beat properties
            "eight_beat_period_pos", # Positivity
            
            # Mass cascade basics
            "mass_formula_pos",    # Mass formula gives positive values
            
            # Exact constants
            "coherence_quantum_pos", # E_coh positivity
            
            # Ledger state basics
            "ledger_state_valid",  # Basic validity
            
            # Pattern basics
            "pattern_layer_nonempty", # Pattern layer exists
            
            # Physics basics
            "particle_mass_pos",   # Particle masses positive
            
            # Complexity basics
            "recognition_cost_pos", # Recognition costs positive
            
            # Gravity basics
            "newton_constant_pos", # G > 0
            
            # LNAL basics
            "assembly_valid",      # Assembly language valid
        ]
        
        # Start with the most important files
        priority_files = [
            "formal/TestSolver.lean",          # Test file first
            "formal/RecognitionScience.lean",  # Main file with golden ratio
            "formal/SimpleWorkingProof.lean",  # Already has working proofs
            "formal/GoldenRatioDemo.lean",     # Golden ratio demonstrations
            "formal/Core/GoldenRatio.lean",    # Core golden ratio theorems
            "formal/Core/ExactConstants.lean", # Basic constants
            "formal/Core/CostFunctional.lean", # Cost functional
            "formal/Basic/LedgerState.lean",   # Basic definitions
            "formal/Physics/CoherenceQuantum.lean", # Physics basics
            "formal/Physics/MassCascade.lean", # Mass calculations
        ]
        
        found_files = []
        for file_path in priority_files:
            if Path(file_path).exists():
                found_files.append(file_path)
                self._scan_file(Path(file_path), whitelist_theorems)
        
        # For now, only scan whitelisted theorems
        print(f"📊 Found {len(self.tasks)} whitelisted theorems to complete")
        print(f"   Starting with easy proofs to test the system")
        
    def _scan_file(self, lean_file: Path, whitelist_theorems: List[str]):
        """Scan a file and extract imports"""
        try:
            content = lean_file.read_text()
            lines = content.split('\n')
            
            # Extract imports
            imports = []
            for line in lines:
                if line.strip().startswith('import'):
                    imports.append(line.strip())
                elif line.strip() and not line.strip().startswith('-'):
                    break  # Stop at first non-import line
            
            # Find sorries
            for i, line in enumerate(lines):
                if 'sorry' in line and not line.strip().startswith('--'):
                    theorem_info = self._extract_theorem_context(lines, i)
                    if theorem_info:
                        if theorem_info['name'] in whitelist_theorems:
                            task = ProofTask(
                                file_path=str(lean_file),
                                theorem_name=theorem_info['name'],
                                theorem_statement=theorem_info['statement'],
                                line_number=i,
                                context=theorem_info['context'],
                                imports=imports
                            )
                            self.tasks.append(task)
        except Exception as e:
            print(f"   ⚠️ Error scanning {lean_file}: {e}")
    
    def _extract_theorem_context(self, lines: List[str], sorry_line: int) -> Optional[Dict]:
        """Extract theorem with more context"""
        theorem_start = None
        for i in range(sorry_line, max(0, sorry_line - 50), -1):
            if any(keyword in lines[i] for keyword in ['theorem', 'lemma', 'def', 'example']):
                theorem_start = i
                break
        
        if theorem_start is None:
            return None
        
        match = re.search(r'(theorem|lemma|def|example)\s+(\w+)', lines[theorem_start])
        if not match:
            return None
        
        theorem_name = match.group(2)
        
        # Get more context
        context_start = max(0, theorem_start - 30)
        context_end = min(len(lines), sorry_line + 20)
        
        return {
            'name': theorem_name,
            'statement': '\n'.join(lines[theorem_start:sorry_line + 1]),
            'context': '\n'.join(lines[context_start:context_end])
        }
    
    def generate_proof(self, task: ProofTask) -> bool:
        """Generate proof with better context"""
        
        prompt = f"""You are proving a theorem in Recognition Science, the formal framework for reality.

THEOREM: {task.theorem_name}
{task.theorem_statement}

FILE: {Path(task.file_path).name}
IMPORTS:
{chr(10).join(task.imports)}

SURROUNDING CONTEXT:
{task.context}

RECOGNITION SCIENCE KEY FACTS:
- φ = (1 + √5)/2 is the golden ratio
- E_coh = 0.090 eV is the coherence quantum  
- τ₀ = 7.33e-15 seconds is the minimal tick
- eight_beat_period = 8 * τ₀
- All masses: E_r = E_coh * φ^r
- J(x) = (x + 1/x)/2 has fixed point φ

LEAN 4 TACTICS (use these exactly):
- rfl (for definitional equality)
- norm_num (for numerical calculations)
- simp (for simplification)
- unfold <name> (to expand definitions)
- positivity (for proving > 0)
- linarith (for linear arithmetic)
- ring (for ring operations)

CRITICAL: Provide ONLY the tactics to replace 'sorry'. 
- Start immediately with the tactic (no 'by')
- Keep it simple (1-3 tactics max)
- For positivity: use 'positivity' or 'norm_num'
- For equations: use 'rfl' or 'simp'
- For arithmetic: use 'norm_num' or 'ring'

Examples:
- For "2 + 2 = 4": just "norm_num"
- For "x > 0" where x is positive constant: just "positivity"
- For definitional equality: just "rfl"

Provide ONLY the tactics, nothing else."""

        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=2000,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            if response.content:
                proof = response.content[0].text.strip()
                
                # Clean the proof
                if proof.startswith('```'):
                    proof = re.sub(r'^```\w*\n', '', proof)
                    proof = re.sub(r'\n```$', '', proof)
                proof = proof.strip()
                
                # Don't add 'by' since we want just the tactics
                if not proof.startswith('by'):
                    proof = 'by ' + proof
                
                # Log the generated proof for debugging
                logging.info(f"   Generated proof: {proof[:100]}...")
                
                if proof and len(proof) > 5 and 'sorry' not in proof.lower():
                    task.proof = proof
                    task.success = True
                    return True
                    
        except Exception as e:
            task.error_msg = str(e)
            print(f"   ❌ API error: {e}")
            
        return False
    
    def verify_and_update(self, task: ProofTask) -> bool:
        """Update file and verify it still builds"""
        try:
            # Read original file
            with open(task.file_path, 'r') as f:
                original_content = f.read()
                lines = original_content.split('\n')
            
            # Replace sorry with the proof
            if task.line_number < len(lines):
                line = lines[task.line_number]
                if 'sorry' in line:
                    # Handle different sorry patterns
                    if ':= sorry' in line:
                        lines[task.line_number] = line.replace('sorry', task.proof)
                    elif 'by sorry' in line:
                        lines[task.line_number] = line.replace('by sorry', task.proof)
                    else:
                        lines[task.line_number] = line.replace('sorry', task.proof)
                    
                    # Write updated file
                    new_content = '\n'.join(lines)
                    with open(task.file_path, 'w') as f:
                        f.write(new_content)
                    
                    # Verify with lake env lean (not lake build)
                    print(f"   🔍 Verifying with lake env lean...")
                    result = subprocess.run(
                        ['lake', 'env', 'lean', task.file_path],
                        capture_output=True,
                        text=True,
                        timeout=30
                    )
                    
                    if result.returncode == 0:
                        task.verified = True
                        print(f"   ✅ Proof verified and file updated!")
                        return True
                    else:
                        # Revert the change
                        with open(task.file_path, 'w') as f:
                            f.write(original_content)
                        
                        # Extract error message
                        error_lines = result.stderr.split('\n') if result.stderr else []
                        for line in error_lines:
                            if 'error:' in line:
                                task.error_msg = line
                                break
                        
                        print(f"   ⚠️ Proof didn't compile, reverted changes")
                        if task.error_msg:
                            print(f"      Error: {task.error_msg[:100]}")
                        # Log full stderr for debugging
                        if result.stderr:
                            logging.debug(f"Full stderr: {result.stderr}")
                        return False
                        
        except Exception as e:
            print(f"   ❌ Update error: {e}")
            task.error_msg = str(e)
            # Ensure we revert on any error
            try:
                with open(task.file_path, 'w') as f:
                    f.write(original_content)
            except:
                pass
            return False
    
    def solve_systematically(self):
        """Solve with focus on success"""
        logging.info("🚀 Beginning systematic proof completion...")
        logging.info("   Focus: Complete proofs that actually compile\n")
        
        start_time = time.time()
        
        # Process theorems
        for i, task in enumerate(self.tasks):
            logging.info(f"\n[{i+1}/{len(self.tasks)}] {task.theorem_name} in {Path(task.file_path).name}")
            
            # Try to generate proof
            if self.generate_proof(task):
                logging.info(f"   🔮 Proof generated")
                
                # Verify and update
                if self.verify_and_update(task):
                    self.completed += 1
                    self.verified += 1
                else:
                    self.failed += 1
            else:
                logging.error(f"   ❌ Could not generate proof")
                self.failed += 1
            
            # Brief pause
            time.sleep(0.5)
            
            # Every 3 successful proofs, run full build check
            if self.completed > 0 and self.completed % 3 == 0:
                logging.info(f"\n🔧 Running full build check after {self.completed} proofs...")
                if self.check_full_build():
                    logging.info("   ✅ Full build still clean!")
                else:
                    logging.error("   ❌ Build broken! Stopping here.")
                    break
        
        # Final summary
        self.print_summary(time.time() - start_time)
    
    def check_full_build(self) -> bool:
        """Run lake build to ensure everything still compiles"""
        result = subprocess.run(
            ['lake', 'build'],
            capture_output=True,
            text=True,
            timeout=120
        )
        return result.returncode == 0
    
    def print_summary(self, elapsed_time):
        """Print results"""
        print(f"\n{'='*60}")
        print(f"UNIVERSE PROOF COMPLETION RESULTS")
        print(f"{'='*60}")
        print(f"Total theorems attempted: {len(self.tasks)}")
        print(f"Successfully proven & verified: {self.completed}")
        print(f"Failed attempts: {self.failed}")
        print(f"Success rate: {self.completed/len(self.tasks)*100:.1f}%" if self.tasks else "N/A")
        print(f"Time elapsed: {elapsed_time/60:.1f} minutes")
        
        if self.completed > 0:
            print(f"\n✨ The formal framework advanced by {self.completed} theorems!")
        
        # Save detailed report
        report = {
            'timestamp': datetime.now().isoformat(),
            'total_attempted': len(self.tasks),
            'completed': self.completed,
            'verified': self.verified,
            'failed': self.failed,
            'time_minutes': elapsed_time/60,
            'completed_theorems': [
                {
                    'name': task.theorem_name,
                    'file': task.file_path,
                    'proof': task.proof
                }
                for task in self.tasks if task.verified
            ]
        }
        
        with open('improved_solver_results.json', 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"\n📄 Detailed results saved to improved_solver_results.json")

def main():
    print("\n🌌 UNIVERSE-LEVEL MANDATE: Complete Recognition Science")
    print("="*60)
    print("Building the formal framework for reality, one proof at a time\n")
    
    solver = ImprovedUniverseSolver()
    solver.scan_priority_files()
    
    if solver.tasks:
        print(f"\n🎯 Ready to complete {len(solver.tasks)} priority proofs")
        solver.solve_systematically()
    else:
        print("✅ No incomplete proofs found in priority files!")

if __name__ == "__main__":
    main() 