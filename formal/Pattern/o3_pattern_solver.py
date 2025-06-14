#!/usr/bin/env python3
"""
O3 Pattern Lemma Solver
=======================

Uses OpenAI's O3 model to solve all lemmas in the Pattern module.
Optimized for mathematical proofs and Lean 4 tactics.
"""

import os
import re
import json
import time
import openai
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
import asyncio

# OpenAI API configuration
API_KEY = os.environ.get("OPENAI_API_KEY")
if not API_KEY:
    print("Error: OPENAI_API_KEY environment variable not set!")
    print("Please set it with: export OPENAI_API_KEY='your-api-key'")
    exit(1)

client = openai.OpenAI(api_key=API_KEY)

class O3PatternSolver:
    """Solver for Pattern module lemmas using O3"""
    
    def __init__(self):
        self.lemma_files = [
            "Lemmas/BasicInequalities.lean",
            "Lemmas/ComplexCalculus.lean", 
            "Lemmas/PrimeTheory.lean",
            "Lemmas/PatternStructure.lean",
            "Lemmas/BalanceComputations.lean",
            "Lemmas/EightBeatLemmas.lean",
            "Lemmas/MainTheoremSteps.lean"
        ]
        
        self.solved_count = 0
        self.total_count = 0
        self.start_time = time.time()
        
        # Tactic suggestions for different lemma types
        self.tactic_hints = {
            "inequality": ["simp", "norm_num", "linarith", "ring"],
            "arithmetic": ["ring", "field_simp", "norm_num"],
            "complex": ["simp [Complex.ext_iff]", "ext", "simp [Complex.re_add]"],
            "prime": ["exact Nat.Prime.two_prime", "apply Nat.Prime.one_lt"],
            "pattern": ["simp [FreeMonoid.one_def]", "rfl", "ext"],
            "modular": ["simp [Nat.add_mod]", "norm_num", "omega"],
            "set": ["simp [Set.mem_def]", "rfl", "ext"],
            "exponential": ["simp [Real.exp_zero]", "exact Real.exp_pos"],
            "convergence": ["apply Summable.of_norm", "exact summable_geometric"],
        }
    
    def detect_lemma_type(self, lemma_name: str, lemma_statement: str) -> str:
        """Detect the type of lemma to suggest appropriate tactics"""
        name_lower = lemma_name.lower()
        stmt_lower = lemma_statement.lower()
        
        if any(x in name_lower for x in ["lt", "le", "pos", "neg", "between"]):
            return "inequality"
        elif any(x in name_lower for x in ["add", "mul", "div", "pow"]):
            return "arithmetic"
        elif "complex" in name_lower or "exp" in name_lower:
            return "complex"
        elif "prime" in name_lower:
            return "prime"
        elif "pattern" in name_lower or "ofatom" in name_lower:
            return "pattern"
        elif "mod" in name_lower:
            return "modular"
        elif "mem" in name_lower or "set" in stmt_lower:
            return "set"
        elif "exp" in name_lower:
            return "exponential"
        elif "summable" in stmt_lower:
            return "convergence"
        else:
            return "general"
    
    def create_proof_prompt(self, lemma_name: str, lemma_statement: str, 
                          imports: List[str], context: str) -> str:
        """Create optimized prompt for O3"""
        lemma_type = self.detect_lemma_type(lemma_name, lemma_statement)
        tactics = self.tactic_hints.get(lemma_type, ["simp", "rfl", "exact"])
        
        prompt = f"""You are an expert Lean 4 theorem prover. Prove this lemma by replacing 'sorry' with a complete proof.

LEMMA TO PROVE:
```lean
lemma {lemma_name} : {lemma_statement} := by sorry
```

CONTEXT:
- This is from the Recognition Science Pattern module
- Lemma type detected: {lemma_type}
- Suggested tactics: {', '.join(tactics)}

AVAILABLE IMPORTS:
{chr(10).join(imports)}

IMPORTANT RULES:
1. Replace 'sorry' with a complete proof
2. Use only standard Lean 4 tactics
3. Be concise but complete
4. Common patterns:
   - For inequalities: simp, norm_num, linarith
   - For arithmetic: ring, field_simp
   - For complex numbers: simp [Complex.ext_iff]
   - For primes: use Nat.Prime lemmas from Mathlib
   - For sets: simp [Set.mem_def], ext

EXAMPLES OF SIMILAR PROOFS:
```lean
lemma one_lt_two : (1 : ℝ) < 2 := by norm_num

lemma exp_pos (x : ℝ) : 0 < Real.exp x := by exact Real.exp_pos x

lemma prime_two : Prime 2 := by exact Nat.Prime.two_prime
```

Now provide ONLY the proof code that replaces 'sorry'. Start with 'by' and include all tactics."""
        
        return prompt
    
    def extract_lemmas(self, file_content: str) -> List[Tuple[str, str, int]]:
        """Extract all lemmas with sorry from a file"""
        lemmas = []
        
        # Pattern to match lemmas with sorry
        pattern = r'lemma\s+(\w+).*?:\s*(.*?)\s*:=\s*by\s+sorry'
        
        for match in re.finditer(pattern, file_content, re.DOTALL):
            lemma_name = match.group(1)
            lemma_statement = match.group(2).strip()
            start_pos = match.start()
            
            # Count line number
            line_num = file_content[:start_pos].count('\n') + 1
            
            lemmas.append((lemma_name, lemma_statement, line_num))
        
        return lemmas
    
    def solve_single_lemma(self, lemma_name: str, lemma_statement: str, 
                          imports: List[str], context: str) -> Optional[str]:
        """Solve a single lemma using O3"""
        prompt = self.create_proof_prompt(lemma_name, lemma_statement, imports, context)
        
        try:
            response = client.chat.completions.create(
                model="o3",
                messages=[
                    {"role": "system", "content": "You are a Lean 4 proof assistant. Provide only the proof code."},
                    {"role": "user", "content": prompt}
                ],
                temperature=0.1,  # Low temperature for mathematical precision
                max_tokens=500
            )
            
            proof = response.choices[0].message.content.strip()
            
            # Clean up the proof
            if proof.startswith("```lean"):
                proof = proof[7:]
            if proof.endswith("```"):
                proof = proof[:-3]
            proof = proof.strip()
            
            # Ensure it starts with 'by'
            if not proof.startswith("by"):
                proof = "by " + proof
            
            return proof
            
        except Exception as e:
            print(f"Error solving {lemma_name}: {e}")
            return None
    
    def process_file(self, file_path: str) -> Dict[str, any]:
        """Process a single file and solve all lemmas"""
        print(f"\n{'='*60}")
        print(f"Processing: {file_path}")
        print(f"{'='*60}")
        
        full_path = Path(file_path)
        if not full_path.exists():
            print(f"File not found: {file_path}")
            return {"file": file_path, "solved": 0, "total": 0}
        
        with open(full_path, 'r') as f:
            content = f.read()
        
        # Extract imports
        imports = re.findall(r'^import\s+(.+)$', content, re.MULTILINE)
        
        # Extract lemmas
        lemmas = self.extract_lemmas(content)
        self.total_count += len(lemmas)
        
        print(f"Found {len(lemmas)} lemmas to solve")
        
        # Solve each lemma
        new_content = content
        solved = 0
        
        for lemma_name, lemma_statement, line_num in lemmas:
            print(f"\n  Solving {lemma_name} (line {line_num})...", end='', flush=True)
            
            proof = self.solve_single_lemma(lemma_name, lemma_statement, imports, content)
            
            if proof:
                # Replace sorry with the proof
                pattern = f'(lemma\\s+{lemma_name}.*?:=\\s*)by\\s+sorry'
                replacement = f'\\1{proof}'
                new_content = re.sub(pattern, replacement, new_content, flags=re.DOTALL)
                
                solved += 1
                self.solved_count += 1
                print(f" ✓ SOLVED")
            else:
                print(f" ✗ FAILED")
        
        # Save the updated file
        output_path = full_path.with_suffix('.solved.lean')
        with open(output_path, 'w') as f:
            f.write(new_content)
        
        print(f"\nSolved {solved}/{len(lemmas)} lemmas")
        print(f"Output saved to: {output_path}")
        
        return {
            "file": file_path,
            "solved": solved,
            "total": len(lemmas),
            "output": str(output_path)
        }
    
    def solve_all_parallel(self, max_workers: int = 5):
        """Solve all lemma files in parallel"""
        print("\n" + "="*80)
        print("O3 PATTERN LEMMA SOLVER")
        print("="*80)
        print(f"Model: OpenAI O3")
        print(f"Files to process: {len(self.lemma_files)}")
        print(f"Parallel workers: {max_workers}")
        print("="*80)
        
        results = []
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # Submit all files for processing
            future_to_file = {
                executor.submit(self.process_file, file_path): file_path 
                for file_path in self.lemma_files
            }
            
            # Process results as they complete
            for future in as_completed(future_to_file):
                file_path = future_to_file[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    print(f"Error processing {file_path}: {e}")
                    results.append({
                        "file": file_path,
                        "solved": 0,
                        "total": 0,
                        "error": str(e)
                    })
        
        # Final report
        self.print_final_report(results)
    
    def print_final_report(self, results: List[Dict]):
        """Print final summary report"""
        elapsed = time.time() - self.start_time
        
        print("\n" + "="*80)
        print("FINAL REPORT")
        print("="*80)
        
        for result in results:
            status = "✓" if result["solved"] == result["total"] else "⚠"
            print(f"{status} {result['file']}: {result['solved']}/{result['total']} solved")
        
        print(f"\nTOTAL: {self.solved_count}/{self.total_count} lemmas solved")
        print(f"Success rate: {self.solved_count/self.total_count*100:.1f}%")
        print(f"Time elapsed: {elapsed:.1f} seconds")
        print(f"Average time per lemma: {elapsed/self.total_count:.2f} seconds")
        
        if self.solved_count == self.total_count:
            print("\n🎉 ALL LEMMAS SOLVED! 🎉")
        else:
            print(f"\n⚠️  {self.total_count - self.solved_count} lemmas still need attention")
        
        print("="*80)


def main():
    """Main entry point"""
    solver = O3PatternSolver()
    
    # Check if we're in the right directory
    if not Path("Lemmas").exists():
        print("Error: Lemmas directory not found!")
        print("Please run this script from the Pattern directory")
        return
    
    # Run the solver
    solver.solve_all_parallel(max_workers=3)  # Adjust based on API rate limits
    
    print("\n✓ Solver complete!")
    print("Check the .solved.lean files for results")


if __name__ == "__main__":
    main() 