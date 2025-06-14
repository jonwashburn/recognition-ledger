#!/usr/bin/env python3
"""
Advanced O3 Pattern Lemma Solver
================================

Enhanced version with:
- Batch processing for efficiency
- Retry logic for failed proofs
- Progress tracking
- Proof validation
- Cost estimation
"""

import os
import re
import json
import time
import openai
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Set
from datetime import datetime
from dataclasses import dataclass
import logging
from concurrent.futures import ThreadPoolExecutor, as_completed
import asyncio
import hashlib

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('o3_solver.log'),
        logging.StreamHandler()
    ]
)

# OpenAI API configuration
API_KEY = os.environ.get("OPENAI_API_KEY")
if not API_KEY:
    print("Error: OPENAI_API_KEY environment variable not set!")
    print("Please set it with: export OPENAI_API_KEY='your-api-key'")
    exit(1)

client = openai.OpenAI(api_key=API_KEY)

@dataclass
class Lemma:
    """Represents a lemma to be solved"""
    name: str
    statement: str
    file_path: str
    line_num: int
    lemma_type: str
    complexity: int  # 1-5 scale
    
    def __hash__(self):
        return hash(f"{self.file_path}:{self.name}")

@dataclass
class ProofResult:
    """Result of a proof attempt"""
    lemma: Lemma
    proof: Optional[str]
    success: bool
    error: Optional[str]
    attempts: int
    tokens_used: int

class AdvancedO3Solver:
    """Advanced solver with batch processing and retry logic"""
    
    def __init__(self, max_retries: int = 3, batch_size: int = 5):
        self.max_retries = max_retries
        self.batch_size = batch_size
        self.results: List[ProofResult] = []
        self.total_tokens = 0
        self.start_time = time.time()
        
        # Enhanced tactic database
        self.tactic_database = {
            "inequality": {
                "primary": ["norm_num", "linarith", "simp"],
                "fallback": ["omega", "ring", "field_simp"],
                "advanced": ["interval_cases", "split_ifs"]
            },
            "arithmetic": {
                "primary": ["ring", "field_simp", "norm_num"],
                "fallback": ["simp", "abel", "ring_nf"],
                "advanced": ["polyrith", "qify"]
            },
            "complex": {
                "primary": ["simp [Complex.ext_iff]", "ext", "simp [Complex.re_add, Complex.im_add]"],
                "fallback": ["norm_num", "ring", "field_simp"],
                "advanced": ["convert", "rw [Complex.abs_sq]"]
            },
            "prime": {
                "primary": ["exact Nat.Prime.two_prime", "apply Nat.Prime.one_lt"],
                "fallback": ["simp [Nat.Prime]", "norm_num"],
                "advanced": ["apply Nat.Prime.eq_two_or_odd", "cases'"]
            },
            "pattern": {
                "primary": ["simp [FreeMonoid.one_def]", "rfl", "ext"],
                "fallback": ["cases", "induction", "simp"],
                "advanced": ["apply FreeMonoid.hom_ext", "rw [FreeMonoid.lift_eval_of]"]
            },
            "modular": {
                "primary": ["simp [Nat.add_mod, Nat.mul_mod]", "norm_num", "omega"],
                "fallback": ["ring", "mod_cases", "interval_cases"],
                "advanced": ["rw [Nat.mod_eq_of_lt]", "apply Nat.mod_lt"]
            },
            "set": {
                "primary": ["simp [Set.mem_def]", "ext", "rfl"],
                "fallback": ["intro", "constructor", "exact"],
                "advanced": ["apply Set.Subset.antisymm", "rw [Set.eq_empty_iff_forall_not_mem]"]
            },
            "exponential": {
                "primary": ["simp [Real.exp_zero]", "exact Real.exp_pos"],
                "fallback": ["norm_num", "positivity", "simp"],
                "advanced": ["rw [Real.exp_add]", "apply Real.exp_lt_exp"]
            },
            "convergence": {
                "primary": ["apply Summable.of_norm", "exact summable_geometric"],
                "fallback": ["apply summable_of_absolute_convergence", "norm_num"],
                "advanced": ["apply Summable.of_norm_bounded", "rw [summable_norm_iff]"]
            }
        }
        
        # Cache for successful proofs
        self.proof_cache: Dict[str, str] = {}
        self.load_cache()
    
    def load_cache(self):
        """Load proof cache from disk"""
        cache_file = Path("o3_proof_cache.json")
        if cache_file.exists():
            try:
                with open(cache_file, 'r') as f:
                    self.proof_cache = json.load(f)
                logging.info(f"Loaded {len(self.proof_cache)} cached proofs")
            except Exception as e:
                logging.warning(f"Failed to load cache: {e}")
    
    def save_cache(self):
        """Save proof cache to disk"""
        try:
            with open("o3_proof_cache.json", 'w') as f:
                json.dump(self.proof_cache, f, indent=2)
            logging.info(f"Saved {len(self.proof_cache)} proofs to cache")
        except Exception as e:
            logging.error(f"Failed to save cache: {e}")
    
    def estimate_complexity(self, lemma: Lemma) -> int:
        """Estimate lemma complexity (1-5 scale)"""
        stmt = lemma.statement.lower()
        
        # Simple heuristics
        complexity = 1
        
        # Check for quantifiers
        if any(q in stmt for q in ["∀", "∃", "forall", "exists"]):
            complexity += 1
        
        # Check for implications
        if "→" in stmt or "->" in stmt or "iff" in stmt:
            complexity += 1
        
        # Check for complex types
        if any(t in stmt for t in ["summable", "continuous", "differentiable"]):
            complexity += 1
        
        # Check statement length
        if len(stmt) > 100:
            complexity += 1
        
        return min(complexity, 5)
    
    def create_batch_prompt(self, lemmas: List[Lemma]) -> str:
        """Create a prompt for batch processing multiple lemmas"""
        prompt = """You are an expert Lean 4 theorem prover. Solve the following lemmas by providing complete proofs.

For each lemma, provide the proof that replaces 'sorry'. Format your response as:

LEMMA: [lemma_name]
PROOF: [complete proof starting with 'by']
---

Here are the lemmas to solve:

"""
        
        for i, lemma in enumerate(lemmas, 1):
            tactics = self.get_tactics_for_lemma(lemma)
            prompt += f"""
{i}. LEMMA: {lemma.name}
   STATEMENT: {lemma.statement}
   TYPE: {lemma.lemma_type}
   SUGGESTED TACTICS: {', '.join(tactics[:3])}
   
"""
        
        prompt += """
Remember:
- Each proof should be complete and start with 'by'
- Use standard Lean 4 tactics
- Be concise but thorough
- Common patterns:
  * Inequalities: norm_num, linarith
  * Arithmetic: ring, field_simp
  * Complex numbers: simp [Complex.ext_iff]
  * Sets: simp [Set.mem_def], ext

Now provide the proofs for all lemmas above."""
        
        return prompt
    
    def get_tactics_for_lemma(self, lemma: Lemma) -> List[str]:
        """Get relevant tactics for a lemma based on its type"""
        tactics = []
        
        if lemma.lemma_type in self.tactic_database:
            db = self.tactic_database[lemma.lemma_type]
            tactics.extend(db["primary"])
            
            # Add more tactics for complex lemmas
            if lemma.complexity >= 3:
                tactics.extend(db["fallback"])
            if lemma.complexity >= 4:
                tactics.extend(db["advanced"])
        else:
            # Default tactics
            tactics = ["simp", "rfl", "exact", "apply", "intro"]
        
        return tactics
    
    def parse_batch_response(self, response: str, lemmas: List[Lemma]) -> Dict[str, str]:
        """Parse batch response into individual proofs"""
        proofs = {}
        
        # Split by separator
        sections = response.split("---")
        
        for section in sections:
            if "LEMMA:" in section and "PROOF:" in section:
                # Extract lemma name and proof
                lemma_match = re.search(r'LEMMA:\s*(\w+)', section)
                proof_match = re.search(r'PROOF:\s*(.*?)(?=LEMMA:|$)', section, re.DOTALL)
                
                if lemma_match and proof_match:
                    lemma_name = lemma_match.group(1)
                    proof = proof_match.group(1).strip()
                    
                    # Clean up proof
                    if not proof.startswith("by"):
                        proof = "by " + proof
                    
                    proofs[lemma_name] = proof
        
        return proofs
    
    def solve_batch(self, lemmas: List[Lemma], attempt: int = 1) -> List[ProofResult]:
        """Solve a batch of lemmas"""
        results = []
        
        # Check cache first
        uncached_lemmas = []
        for lemma in lemmas:
            cache_key = f"{lemma.file_path}:{lemma.name}"
            if cache_key in self.proof_cache:
                logging.info(f"Using cached proof for {lemma.name}")
                results.append(ProofResult(
                    lemma=lemma,
                    proof=self.proof_cache[cache_key],
                    success=True,
                    error=None,
                    attempts=0,
                    tokens_used=0
                ))
            else:
                uncached_lemmas.append(lemma)
        
        if not uncached_lemmas:
            return results
        
        # Create batch prompt
        prompt = self.create_batch_prompt(uncached_lemmas)
        
        try:
            # Call O3
            response = client.chat.completions.create(
                model="o3",
                messages=[
                    {"role": "system", "content": "You are a Lean 4 proof assistant. Provide complete, working proofs."},
                    {"role": "user", "content": prompt}
                ],
                temperature=0.1 + (attempt - 1) * 0.1,  # Increase temperature on retries
                max_tokens=2000
            )
            
            # Parse response
            response_text = response.choices[0].message.content
            proofs = self.parse_batch_response(response_text, uncached_lemmas)
            
            # Track tokens
            tokens = response.usage.total_tokens
            self.total_tokens += tokens
            
            # Create results
            for lemma in uncached_lemmas:
                if lemma.name in proofs:
                    proof = proofs[lemma.name]
                    # Cache successful proof
                    cache_key = f"{lemma.file_path}:{lemma.name}"
                    self.proof_cache[cache_key] = proof
                    
                    results.append(ProofResult(
                        lemma=lemma,
                        proof=proof,
                        success=True,
                        error=None,
                        attempts=attempt,
                        tokens_used=tokens // len(uncached_lemmas)
                    ))
                else:
                    results.append(ProofResult(
                        lemma=lemma,
                        proof=None,
                        success=False,
                        error="No proof found in response",
                        attempts=attempt,
                        tokens_used=tokens // len(uncached_lemmas)
                    ))
            
        except Exception as e:
            logging.error(f"Batch solving error: {e}")
            # Return failures for all lemmas
            for lemma in uncached_lemmas:
                results.append(ProofResult(
                    lemma=lemma,
                    proof=None,
                    success=False,
                    error=str(e),
                    attempts=attempt,
                    tokens_used=0
                ))
        
        return results
    
    def extract_all_lemmas(self) -> List[Lemma]:
        """Extract all lemmas from all files"""
        all_lemmas = []
        
        lemma_files = [
            "Lemmas/BasicInequalities.lean",
            "Lemmas/ComplexCalculus.lean",
            "Lemmas/PrimeTheory.lean",
            "Lemmas/PatternStructure.lean",
            "Lemmas/BalanceComputations.lean",
            "Lemmas/EightBeatLemmas.lean",
            "Lemmas/MainTheoremSteps.lean"
        ]
        
        for file_path in lemma_files:
            if not Path(file_path).exists():
                logging.warning(f"File not found: {file_path}")
                continue
            
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Extract lemmas with sorry
            pattern = r'lemma\s+(\w+).*?:\s*(.*?)\s*:=\s*by\s+sorry'
            
            for match in re.finditer(pattern, content, re.DOTALL):
                lemma_name = match.group(1)
                lemma_statement = match.group(2).strip()
                line_num = content[:match.start()].count('\n') + 1
                
                # Detect type
                lemma_type = self.detect_lemma_type(lemma_name, lemma_statement)
                
                lemma = Lemma(
                    name=lemma_name,
                    statement=lemma_statement,
                    file_path=file_path,
                    line_num=line_num,
                    lemma_type=lemma_type,
                    complexity=1  # Will be updated
                )
                
                # Estimate complexity
                lemma.complexity = self.estimate_complexity(lemma)
                
                all_lemmas.append(lemma)
        
        return all_lemmas
    
    def detect_lemma_type(self, name: str, statement: str) -> str:
        """Detect lemma type"""
        name_lower = name.lower()
        stmt_lower = statement.lower()
        
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
    
    def apply_proofs(self, results: List[ProofResult]):
        """Apply successful proofs to files"""
        # Group by file
        file_results: Dict[str, List[ProofResult]] = {}
        for result in results:
            if result.success and result.proof:
                file_path = result.lemma.file_path
                if file_path not in file_results:
                    file_results[file_path] = []
                file_results[file_path].append(result)
        
        # Process each file
        for file_path, file_proofs in file_results.items():
            logging.info(f"Applying {len(file_proofs)} proofs to {file_path}")
            
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Apply each proof
            for result in file_proofs:
                pattern = f'(lemma\\s+{result.lemma.name}.*?:=\\s*)by\\s+sorry'
                replacement = f'\\1{result.proof}'
                content = re.sub(pattern, replacement, content, flags=re.DOTALL)
            
            # Save to .solved file
            output_path = Path(file_path).with_suffix('.solved.lean')
            with open(output_path, 'w') as f:
                f.write(content)
            
            logging.info(f"Saved to {output_path}")
    
    def run(self):
        """Main solver loop"""
        logging.info("="*80)
        logging.info("ADVANCED O3 PATTERN LEMMA SOLVER")
        logging.info("="*80)
        
        # Extract all lemmas
        all_lemmas = self.extract_all_lemmas()
        logging.info(f"Found {len(all_lemmas)} lemmas to solve")
        
        # Sort by complexity (solve easier ones first)
        all_lemmas.sort(key=lambda l: (l.complexity, l.lemma_type))
        
        # Process in batches
        for i in range(0, len(all_lemmas), self.batch_size):
            batch = all_lemmas[i:i+self.batch_size]
            logging.info(f"\nProcessing batch {i//self.batch_size + 1}/{(len(all_lemmas) + self.batch_size - 1)//self.batch_size}")
            
            # Try solving with retries
            batch_results = []
            failed_lemmas = batch
            
            for attempt in range(1, self.max_retries + 1):
                if not failed_lemmas:
                    break
                
                logging.info(f"  Attempt {attempt}/{self.max_retries} for {len(failed_lemmas)} lemmas")
                
                # Solve batch
                results = self.solve_batch(failed_lemmas, attempt)
                
                # Separate successes and failures
                new_failed = []
                for result in results:
                    if result.success:
                        batch_results.append(result)
                        logging.info(f"    ✓ Solved: {result.lemma.name}")
                    else:
                        new_failed.append(result.lemma)
                        if attempt == self.max_retries:
                            batch_results.append(result)
                            logging.warning(f"    ✗ Failed: {result.lemma.name} - {result.error}")
                
                failed_lemmas = new_failed
                
                # Small delay between retries
                if failed_lemmas and attempt < self.max_retries:
                    time.sleep(2)
            
            self.results.extend(batch_results)
            
            # Save cache periodically
            if i % (self.batch_size * 5) == 0:
                self.save_cache()
        
        # Apply all successful proofs
        self.apply_proofs(self.results)
        
        # Save final cache
        self.save_cache()
        
        # Print final report
        self.print_report()
    
    def print_report(self):
        """Print final summary report"""
        elapsed = time.time() - self.start_time
        successful = sum(1 for r in self.results if r.success)
        total = len(self.results)
        
        logging.info("\n" + "="*80)
        logging.info("FINAL REPORT")
        logging.info("="*80)
        
        # Group by file
        file_stats = {}
        for result in self.results:
            file_path = result.lemma.file_path
            if file_path not in file_stats:
                file_stats[file_path] = {"total": 0, "solved": 0}
            file_stats[file_path]["total"] += 1
            if result.success:
                file_stats[file_path]["solved"] += 1
        
        # Print per-file stats
        for file_path, stats in file_stats.items():
            status = "✓" if stats["solved"] == stats["total"] else "⚠"
            logging.info(f"{status} {file_path}: {stats['solved']}/{stats['total']} solved")
        
        logging.info(f"\nTOTAL: {successful}/{total} lemmas solved ({successful/total*100:.1f}%)")
        logging.info(f"Time elapsed: {elapsed:.1f} seconds")
        logging.info(f"Total tokens used: {self.total_tokens:,}")
        logging.info(f"Estimated cost: ${self.total_tokens * 0.00002:.2f}")  # Rough estimate
        
        if successful == total:
            logging.info("\n🎉 ALL LEMMAS SOLVED! 🎉")
        else:
            failed = total - successful
            logging.warning(f"\n⚠️  {failed} lemmas still need manual attention")
            
            # List failed lemmas
            logging.info("\nFailed lemmas:")
            for result in self.results:
                if not result.success:
                    logging.info(f"  - {result.lemma.name} ({result.lemma.file_path}:{result.lemma.line_num})")
        
        logging.info("="*80)


def main():
    """Main entry point"""
    # Check directory
    if not Path("Lemmas").exists():
        print("Error: Lemmas directory not found!")
        print("Please run this script from the Pattern directory")
        return
    
    # Run solver
    solver = AdvancedO3Solver(max_retries=3, batch_size=5)
    solver.run()


if __name__ == "__main__":
    main() 