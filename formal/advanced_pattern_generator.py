#!/usr/bin/env python3
"""
Advanced Pattern Generator for Recognition Science
Generates multiplication tables, powers, and more complex patterns
"""

from typing import List, Tuple

class AdvancedPatternGenerator:
    def __init__(self):
        self.num_words = {
            0: "zero", 1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
            6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten",
            11: "eleven", 12: "twelve", 13: "thirteen", 14: "fourteen", 15: "fifteen",
            16: "sixteen", 17: "seventeen", 18: "eighteen", 19: "nineteen", 20: "twenty",
            21: "twentyone", 22: "twentytwo", 23: "twentythree", 24: "twentyfour", 25: "twentyfive",
            30: "thirty", 36: "thirtysix", 40: "forty", 42: "fortytwo", 45: "fortyfive",
            48: "fortyeight", 49: "fortynine", 50: "fifty", 54: "fiftyfour", 56: "fiftysix",
            60: "sixty", 63: "sixtythree", 64: "sixtyfour", 70: "seventy", 72: "seventytwo",
            80: "eighty", 81: "eightyone", 90: "ninety", 100: "hundred"
        }
    
    def num_to_word(self, n: int) -> str:
        """Convert number to word for theorem names"""
        return self.num_words.get(n, f"n{n}")
    
    def generate_multiplication_tables(self) -> List[Tuple[str, str]]:
        """Generate multiplication tables 1-10"""
        theorems = []
        
        for i in range(1, 11):
            for j in range(1, 11):
                result = i * j
                name = f"mul_{self.num_to_word(i)}_{self.num_to_word(j)}"
                theorem = f"theorem {name} : {i} * {j} = {result} := by rfl"
                theorems.append((name, theorem))
        
        return theorems
    
    def generate_squares_and_cubes(self) -> List[Tuple[str, str]]:
        """Generate squares and cubes for 1-10"""
        theorems = []
        
        # Squares
        for i in range(1, 11):
            square = i * i
            name = f"square_{self.num_to_word(i)}"
            theorem = f"theorem {name} : {i}^2 = {square} := by norm_num"
            theorems.append((name, theorem))
        
        # Cubes
        for i in range(1, 8):  # Keep cubes smaller
            cube = i * i * i
            name = f"cube_{self.num_to_word(i)}"
            theorem = f"theorem {name} : {i}^3 = {cube} := by norm_num"
            theorems.append((name, theorem))
        
        return theorems
    
    def generate_division_theorems(self) -> List[Tuple[str, str]]:
        """Generate exact division theorems"""
        theorems = []
        
        # Common divisions
        divisions = [
            (10, 2, 5), (20, 4, 5), (30, 5, 6), (40, 8, 5),
            (50, 10, 5), (60, 12, 5), (100, 20, 5), (100, 25, 4),
            (36, 6, 6), (48, 8, 6), (72, 9, 8), (81, 9, 9)
        ]
        
        for a, b, result in divisions:
            name = f"div_{self.num_to_word(a)}_{self.num_to_word(b)}"
            theorem = f"theorem {name} : {a} / {b} = {result} := by norm_num"
            theorems.append((name, theorem))
        
        return theorems
    
    def generate_sum_formulas(self) -> List[Tuple[str, str]]:
        """Generate sum formulas (1+2+...+n)"""
        theorems = []
        
        for n in [3, 4, 5, 6, 7, 8, 9, 10]:
            sum_val = n * (n + 1) // 2
            name = f"sum_to_{self.num_to_word(n)}"
            # We'll use a simple explicit sum for now
            sum_expr = " + ".join(str(i) for i in range(1, n+1))
            theorem = f"theorem {name} : {sum_expr} = {sum_val} := by norm_num"
            theorems.append((name, theorem))
        
        return theorems
    
    def generate_recognition_constants(self) -> List[Tuple[str, str]]:
        """Generate more Recognition Science constant theorems"""
        theorems = []
        constants = [
            ("E_coh", "E_coh"),
            ("τ₀", "tau_zero"),
            ("eight_beat_period", "eight_beat")
        ]
        
        for const, const_name in constants:
            # Squared positivity
            theorems.append((
                f"{const_name}_squared_pos",
                f"theorem {const_name}_squared_pos : {const}^2 > 0 := by\n  unfold {const}\n  norm_num"
            ))
            
            # Sum with itself
            theorems.append((
                f"{const_name}_double_formula",
                f"theorem {const_name}_double_formula : {const} + {const} = 2 * {const} := by ring"
            ))
            
            # Triple
            theorems.append((
                f"{const_name}_triple_pos",
                f"theorem {const_name}_triple_pos : 3 * {const} > 0 := by\n  unfold {const}\n  norm_num"
            ))
        
        return theorems
    
    def generate_lean_file(self, filename: str = "AdvancedBatch.lean"):
        """Generate complete Lean file with all advanced theorems"""
        
        # Generate all theorem categories
        multiplication = self.generate_multiplication_tables()
        squares_cubes = self.generate_squares_and_cubes()
        divisions = self.generate_division_theorems()
        sums = self.generate_sum_formulas()
        constants = self.generate_recognition_constants()
        
        content = """/-
Advanced auto-generated theorems for Recognition Science
Generated by advanced_pattern_generator.py
-/

import RecognitionScience

namespace AdvancedBatch

open RecognitionScience

/-! ## Multiplication Tables (1-10) -/

"""
        
        # Add multiplication tables
        for name, theorem in multiplication[:50]:  # First 50
            content += theorem + "\n\n"
        
        content += "/-! ## Squares and Cubes -/\n\n"
        
        for name, theorem in squares_cubes:
            content += theorem + "\n\n"
        
        content += "/-! ## Division Theorems -/\n\n"
        
        for name, theorem in divisions:
            content += theorem + "\n\n"
        
        content += "/-! ## Sum Formulas -/\n\n"
        
        for name, theorem in sums:
            content += theorem + "\n\n"
        
        content += "/-! ## Recognition Science Constants -/\n\n"
        
        for name, theorem in constants:
            content += theorem + "\n\n"
        
        content += "end AdvancedBatch\n"
        
        with open(f"formal/{filename}", 'w') as f:
            f.write(content)
        
        total = min(50, len(multiplication)) + len(squares_cubes) + len(divisions) + len(sums) + len(constants)
        
        print(f"Generated {filename} with {total} theorems:")
        print(f"  - Multiplication tables: {min(50, len(multiplication))} theorems")
        print(f"  - Squares and cubes: {len(squares_cubes)} theorems")
        print(f"  - Division: {len(divisions)} theorems")
        print(f"  - Sum formulas: {len(sums)} theorems")
        print(f"  - Constants: {len(constants)} theorems")
        
        return total

if __name__ == "__main__":
    generator = AdvancedPatternGenerator()
    total = generator.generate_lean_file("AdvancedBatch.lean")
    print(f"\n✅ Successfully generated {total} advanced theorems!") 