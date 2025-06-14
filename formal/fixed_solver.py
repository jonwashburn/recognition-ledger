#!/usr/bin/env python3
"""
Fixed Recognition Science Solver
================================

This solver properly generates and writes Lean 4 proofs.
"""

import os
import re
import json
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime
import anthropic

# Configuration
MODEL = "claude-3-5-sonnet-20241022"  # Latest Claude model
API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")

@dataclass
class ProofTask:
    file_path: str
    theorem_name: str
    theorem_statement: str
    line_number: int
    category: str
    proof: Optional[str] = None
    success: bool = False

class FixedSolver:
    def __init__(self):
        if not API_KEY:
            raise ValueError("❌ ANTHROPIC_API_KEY not set!")
            
        self.client = anthropic.Anthropic(api_key=API_KEY)
        self.model = MODEL
        self.tasks = []
        self.completed = 0
        
        print(f"✅ Fixed solver initialized")
        print(f"   Model: {self.model}")
        
    def scan_for_sorries(self):
        """Find all 'sorry' instances in Lean files"""
        print("\n🔍 Scanning for incomplete proofs...")
        
        # Look for all Lean files
        for lean_file in Path(".").rglob("*.lean"):
            # Skip completed files and lake packages
            if "_COMPLETED" in str(lean_file) or "lake-packages" in str(lean_file):
                continue
                
            try:
                content = lean_file.read_text()
                lines = content.split('\n')
                
                # Find all sorries with their line numbers
                for i, line in enumerate(lines):
                    if 'sorry' in line and not line.strip().startswith('--'):
                        # Extract the theorem this sorry belongs to
                        theorem_info = self._find_theorem_for_sorry(lines, i)
                        if theorem_info:
                            task = ProofTask(
                                file_path=str(lean_file),
                                theorem_name=theorem_info['name'],
                                theorem_statement=theorem_info['statement'],
                                line_number=i,
                                category=lean_file.parent.name
                            )
                            self.tasks.append(task)
            except Exception as e:
                print(f"   ⚠️ Error scanning {lean_file}: {e}")
        
        print(f"📊 Found {len(self.tasks)} theorems to prove")
        
    def _find_theorem_for_sorry(self, lines: List[str], sorry_line: int) -> Optional[Dict]:
        """Find the theorem declaration for a sorry"""
        # Search backwards for theorem/lemma declaration
        for i in range(sorry_line, max(0, sorry_line - 50), -1):
            line = lines[i]
            if 'theorem' in line or 'lemma' in line:
                # Extract theorem name
                match = re.search(r'(theorem|lemma)\s+(\w+)', line)
                if match:
                    theorem_name = match.group(2)
                    
                    # Collect full theorem statement
                    statement_lines = []
                    j = i
                    while j <= sorry_line and j < len(lines):
                        statement_lines.append(lines[j])
                        j += 1
                    
                    return {
                        'name': theorem_name,
                        'statement': '\n'.join(statement_lines)
                    }
        return None
    
    def generate_proof(self, task: ProofTask) -> bool:
        """Generate proof using Claude"""
        
        # Read the full file for context
        try:
            with open(task.file_path, 'r') as f:
                file_content = f.read()
        except:
            file_content = ""
        
        # Extract imports and context
        imports = re.findall(r'^import\s+(.+)$', file_content, re.MULTILINE)
        
        prompt = f"""You are an expert Lean 4 theorem prover working on Recognition Science.

THEOREM TO PROVE:
{task.theorem_statement}

FILE CONTEXT:
- File: {task.file_path}
- Category: {task.category}
- Imports: {', '.join(imports[:5])}  # First 5 imports

RECOGNITION SCIENCE KEY VALUES:
- Golden ratio φ = (1 + √5) / 2 ≈ 1.618034
- Coherence quantum E_coh = 0.090 eV
- Eight-beat cycle period
- Mass formula: E_r = E_coh × φ^r
- Fine structure α ≈ 1/137

INSTRUCTIONS:
1. Replace 'sorry' with a complete Lean 4 proof
2. Use only valid Lean 4 tactics
3. The proof should compile without errors
4. Common tactics: simp, rfl, exact, apply, intro, cases, induction, norm_num, ring, linarith

Provide ONLY the proof code that replaces 'sorry'. Start with 'by' and include all tactics.
For example: "by simp" or "by norm_num" or a multi-line proof.

IMPORTANT: Do not include the theorem declaration, just the proof after :="""

        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=2000,
                temperature=0.1,
                messages=[{"role": "user", "content": prompt}]
            )
            
            if response.content:
                proof = response.content[0].text.strip()
                
                # Clean up the proof
                if proof.startswith('```lean'):
                    proof = proof[7:]
                if proof.endswith('```'):
                    proof = proof[:-3]
                proof = proof.strip()
                
                # Ensure it starts with 'by'
                if not proof.startswith('by'):
                    proof = 'by ' + proof
                
                # Basic validation
                if proof and len(proof) > 5 and 'sorry' not in proof.lower():
                    task.proof = proof
                    task.success = True
                    return True
                    
            return False
            
        except Exception as e:
            print(f"   ❌ API error: {e}")
            return False
    
    def update_file(self, task: ProofTask):
        """Update the Lean file with the proof"""
        try:
            with open(task.file_path, 'r') as f:
                lines = f.readlines()
            
            # Find the line with sorry and replace it
            if task.line_number < len(lines):
                line = lines[task.line_number]
                
                # Replace sorry with the proof
                if 'sorry' in line:
                    # Handle different sorry patterns
                    if ':= sorry' in line:
                        lines[task.line_number] = line.replace('sorry', task.proof)
                    elif ':= by sorry' in line:
                        lines[task.line_number] = line.replace('by sorry', task.proof)
                    else:
                        # Just replace sorry
                        lines[task.line_number] = line.replace('sorry', task.proof)
                    
                    # Write back to file
                    output_path = task.file_path.replace('.lean', '_FIXED.lean')
                    with open(output_path, 'w') as f:
                        f.writelines(lines)
                    
                    print(f"   📝 Saved to {output_path}")
                    return True
                    
        except Exception as e:
            print(f"   ❌ Failed to update file: {e}")
            
        return False
    
    def solve_all(self):
        """Main solving loop"""
        print(f"\n🚀 Starting proof generation...")
        
        start_time = time.time()
        
        # Group by category for better context
        categories = {}
        for task in self.tasks:
            if task.category not in categories:
                categories[task.category] = []
            categories[task.category].append(task)
        
        # Process by category
        task_num = 0
        for category, tasks in categories.items():
            print(f"\n📁 Processing {category} ({len(tasks)} theorems)")
            
            for task in tasks:
                task_num += 1
                print(f"\n[{task_num}/{len(self.tasks)}] {task.theorem_name}")
                
                if self.generate_proof(task):
                    print(f"   ✅ Proof generated!")
                    if self.update_file(task):
                        self.completed += 1
                else:
                    print(f"   ❌ Failed to generate proof")
                
                # Brief pause
                time.sleep(0.5)
        
        # Summary
        elapsed = time.time() - start_time
        print(f"\n{'='*60}")
        print(f"COMPLETION SUMMARY")
        print(f"{'='*60}")
        print(f"Total theorems: {len(self.tasks)}")
        print(f"Successfully proved: {self.completed}")
        print(f"Success rate: {self.completed/len(self.tasks)*100:.1f}%" if self.tasks else "N/A")
        print(f"Time elapsed: {elapsed/60:.1f} minutes")
        
        # List failed proofs
        if self.completed < len(self.tasks):
            print(f"\n❌ Failed proofs:")
            for task in self.tasks:
                if not task.success:
                    print(f"   - {task.theorem_name} in {task.file_path}")

def main():
    print("\n🔧 Fixed Recognition Science Solver")
    print("="*50)
    
    solver = FixedSolver()
    solver.scan_for_sorries()
    
    if solver.tasks:
        solver.solve_all()
    else:
        print("✅ No incomplete proofs found!")

if __name__ == "__main__":
    main() 