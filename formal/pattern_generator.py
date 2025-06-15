#!/usr/bin/env python3
"""
Pattern-based Theorem Generator for Recognition Science
Generates theorems using proven working patterns
"""

import random
from typing import List, Tuple

class PatternGenerator:
    def __init__(self):
        self.arithmetic_ops = [
            ('+', 'plus'),
            ('*', 'times'),
            ('-', 'minus')
        ]
        
        self.comparison_ops = [
            ('>', 'gt'),
            ('≥', 'ge'),
            ('<', 'lt'),
            ('≤', 'le')
        ]
        
        self.constants = [
            ('E_coh', 'E_coh'),
            ('τ₀', 'tau_zero'),
            ('eight_beat_period', 'eight_beat')
        ]
    
    def generate_arithmetic_theorems(self, count: int = 20) -> List[Tuple[str, str, str]]:
        """Generate arithmetic theorems using Pattern 1 (rfl)"""
        theorems = []
        used = set()
        
        while len(theorems) < count:
            a = random.randint(1, 20)
            b = random.randint(1, 20)
            op, op_name = random.choice(self.arithmetic_ops)
            
            if op == '+':
                result = a + b
            elif op == '*':
                result = a * b
            elif op == '-' and a > b:
                result = a - b
            else:
                continue
            
            name = f"{self._num_to_word(a)}_{op_name}_{self._num_to_word(b)}"
            if name not in used:
                used.add(name)
                theorem = f"theorem {name} : {a} {op} {b} = {result} := by rfl"
                theorems.append((name, theorem, "rfl"))
        
        return theorems
    
    def generate_inequality_theorems(self, count: int = 20) -> List[Tuple[str, str, str]]:
        """Generate inequality theorems using Pattern 2 (norm_num)"""
        theorems = []
        used = set()
        
        while len(theorems) < count:
            a = random.randint(1, 30)
            b = random.randint(1, 30)
            op, op_name = random.choice(self.comparison_ops)
            
            # Ensure the inequality is true
            if op == '>' and a <= b:
                a, b = b + random.randint(1, 5), b
            elif op == '<' and a >= b:
                a, b = b, b + random.randint(1, 5)
            elif op == '≥' and a < b:
                a = b + random.randint(0, 5)
            elif op == '≤' and a > b:
                b = a + random.randint(0, 5)
            
            name = f"{self._num_to_word(a)}_{op_name}_{self._num_to_word(b)}"
            if name not in used:
                used.add(name)
                theorem = f"theorem {name} : {a} {op} {b} := by norm_num"
                theorems.append((name, theorem, "norm_num"))
        
        return theorems
    
    def generate_constant_theorems(self, count: int = 15) -> List[Tuple[str, str, str]]:
        """Generate constant positivity theorems using Pattern 3 (unfold + norm_num)"""
        theorems = []
        
        for const, const_name in self.constants:
            # Basic positivity
            theorems.append((
                f"{const_name}_pos",
                f"theorem {const_name}_pos : {const} > 0 := by\n  unfold {const}\n  norm_num",
                "unfold+norm_num"
            ))
            
            # Multiplied by positive number
            for n in [2, 3, 5, 10]:
                theorems.append((
                    f"{const_name}_times_{n}_pos",
                    f"theorem {const_name}_times_{n}_pos : {const} * {n} > 0 := by\n  unfold {const}\n  norm_num",
                    "unfold+norm_num"
                ))
            
            # Added to positive number
            for n in [1, 5, 10]:
                theorems.append((
                    f"{const_name}_plus_{n}_gt_{n}",
                    f"theorem {const_name}_plus_{n}_gt_{n} : {const} + {n} > {n} := by\n  unfold {const}\n  norm_num",
                    "unfold+norm_num"
                ))
        
        return theorems[:count]
    
    def _num_to_word(self, n: int) -> str:
        """Convert number to word for theorem names"""
        words = {
            1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
            6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten",
            11: "eleven", 12: "twelve", 13: "thirteen", 14: "fourteen", 15: "fifteen",
            16: "sixteen", 17: "seventeen", 18: "eighteen", 19: "nineteen", 20: "twenty",
            21: "twentyone", 22: "twentytwo", 23: "twentythree", 24: "twentyfour", 25: "twentyfive",
            26: "twentysix", 27: "twentyseven", 28: "twentyeight", 29: "twentynine", 30: "thirty"
        }
        return words.get(n, f"n{n}")
    
    def generate_lean_file(self, filename: str = "GeneratedBatch.lean"):
        """Generate a complete Lean file with all theorems"""
        arithmetic = self.generate_arithmetic_theorems(20)
        inequalities = self.generate_inequality_theorems(20)
        constants = self.generate_constant_theorems(15)
        
        content = """/-
Auto-generated theorems using proven patterns
Generated by pattern_generator.py
-/

import RecognitionScience

namespace GeneratedBatch

open RecognitionScience

/-! ## Pattern 1: Basic Arithmetic (rfl) -/

"""
        
        for name, theorem, _ in arithmetic:
            content += theorem + "\n\n"
        
        content += "/-! ## Pattern 2: Inequalities (norm_num) -/\n\n"
        
        for name, theorem, _ in inequalities:
            content += theorem + "\n\n"
        
        content += "/-! ## Pattern 3: Constant Positivity (unfold + norm_num) -/\n\n"
        
        for name, theorem, _ in constants:
            content += theorem + "\n\n"
        
        content += "end GeneratedBatch\n"
        
        with open(f"formal/{filename}", 'w') as f:
            f.write(content)
        
        total = len(arithmetic) + len(inequalities) + len(constants)
        print(f"Generated {filename} with {total} theorems:")
        print(f"  - Pattern 1 (arithmetic): {len(arithmetic)} theorems")
        print(f"  - Pattern 2 (inequalities): {len(inequalities)} theorems")
        print(f"  - Pattern 3 (constants): {len(constants)} theorems")
        
        return total

if __name__ == "__main__":
    generator = PatternGenerator()
    total = generator.generate_lean_file("GeneratedBatch.lean")
    print(f"\n✅ Successfully generated {total} theorems!") 