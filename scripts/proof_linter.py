#!/usr/bin/env python3
"""
Proof Linter for Recognition Science Lean Formalization

Checks for:
- Trivial proofs masquerading as real proofs
- Numerical constants that should be exact rationals
- Missing strict-mode tags
- Axiom dependencies
"""

import os
import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Set, Tuple

@dataclass
class ProofIssue:
    file: str
    line: int
    issue_type: str
    description: str
    severity: str  # "error", "warning", "info"

class ProofLinter:
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.issues: List[ProofIssue] = []
        
        # Patterns that indicate weak proofs
        self.weak_proof_patterns = [
            (r'by\s+rfl\s*$', "Trivial reflexivity used for non-definitional equality"),
            (r'exact\s+le_refl\s*_', "Trivial inequality reflexivity"),
            (r'exact\s+rfl\s*$', "Reflexivity for complex claim"),
            (r'by\s+ring\s*$', "Ring tactic with no actual algebra"),
            (r'by\s+simp\s*$', "Simp with no lemmas"),
        ]
        
        # Patterns for numerical issues
        self.numerical_patterns = [
            (r'\b\d+\.\d+e[+-]?\d+\b', "Scientific notation should be exact rational"),
            (r'norm_num.*\d+\.\d+', "Decimal in norm_num - use rational"),
            (r'Float\.ofNat', "Float conversion - use rationals"),
        ]
        
        # Files that should have strict mode
        self.should_be_strict = [
            "Core/GoldenRatio_COMPLETED.lean",
            "Physics/CoherenceQuantum_COMPLETED.lean", 
            "Gravity/EinsteinEquations_COMPLETED.lean",
        ]
        
    def lint_file(self, filepath: Path) -> None:
        """Lint a single Lean file."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = f.readlines()
        except Exception as e:
            print(f"Error reading {filepath}: {e}")
            return
            
        relative_path = filepath.relative_to(self.root_dir)
        is_strict = self._is_strict_mode(lines)
        
        # Check if file should be strict but isn't
        if str(relative_path) in self.should_be_strict and not is_strict:
            self.issues.append(ProofIssue(
                file=str(relative_path),
                line=1,
                issue_type="missing_strict",
                description="Completed file should have @strict tag",
                severity="warning"
            ))
        
        for i, line in enumerate(lines, 1):
            # Skip comments and strings
            if line.strip().startswith('--') or line.strip().startswith('/-'):
                continue
                
            # Check weak proofs (only in strict mode)
            if is_strict:
                for pattern, desc in self.weak_proof_patterns:
                    if re.search(pattern, line):
                        self.issues.append(ProofIssue(
                            file=str(relative_path),
                            line=i,
                            issue_type="weak_proof",
                            description=desc,
                            severity="error"
                        ))
            
            # Check numerical issues
            for pattern, desc in self.numerical_patterns:
                if re.search(pattern, line):
                    self.issues.append(ProofIssue(
                        file=str(relative_path),
                        line=i,
                        issue_type="numerical",
                        description=desc,
                        severity="warning"
                    ))
            
            # Check for axioms outside PhysicalPostulates.lean
            if "PhysicalPostulates" not in str(relative_path):
                if re.match(r'^\s*axiom\s+', line):
                    self.issues.append(ProofIssue(
                        file=str(relative_path),
                        line=i,
                        issue_type="unauthorized_axiom",
                        description="Axiom outside PhysicalPostulates.lean",
                        severity="error"
                    ))
    
    def _is_strict_mode(self, lines: List[str]) -> bool:
        """Check if file has @strict tag."""
        for line in lines[:20]:  # Check first 20 lines
            if '@strict' in line:
                return True
        return False
    
    def analyze_axiom_dependencies(self) -> None:
        """Track which files depend on physical postulates."""
        postulates_file = self.root_dir / "PhysicalPostulates.lean"
        if not postulates_file.exists():
            return
            
        # Find all axioms in PhysicalPostulates
        axioms = set()
        try:
            with open(postulates_file, 'r') as f:
                for line in f:
                    match = re.match(r'^\s*axiom\s+(\w+)', line)
                    if match:
                        axioms.add(match.group(1))
        except:
            return
        
        # Check all files for axiom usage
        for lean_file in self.root_dir.rglob("*.lean"):
            if lean_file.name == "PhysicalPostulates.lean":
                continue
                
            try:
                with open(lean_file, 'r') as f:
                    content = f.read()
                    for axiom in axioms:
                        if axiom in content:
                            self.issues.append(ProofIssue(
                                file=str(lean_file.relative_to(self.root_dir)),
                                line=0,
                                issue_type="axiom_dependency",
                                description=f"Depends on axiom: {axiom}",
                                severity="info"
                            ))
                            break
            except:
                continue
    
    def run(self) -> int:
        """Run linter on all Lean files."""
        formal_dir = self.root_dir / "formal"
        if not formal_dir.exists():
            print(f"Error: {formal_dir} does not exist")
            return 1
            
        # Lint all Lean files
        for lean_file in formal_dir.rglob("*.lean"):
            if ".lake" in str(lean_file):
                continue
            self.lint_file(lean_file)
        
        # Analyze axiom dependencies
        self.analyze_axiom_dependencies()
        
        # Report results
        return self.report()
    
    def report(self) -> int:
        """Print linting report and return exit code."""
        if not self.issues:
            print("✅ No proof quality issues found!")
            return 0
        
        # Group by severity
        errors = [i for i in self.issues if i.severity == "error"]
        warnings = [i for i in self.issues if i.severity == "warning"]
        infos = [i for i in self.issues if i.severity == "info"]
        
        print(f"\n🔍 Proof Linting Report")
        print(f"{'='*60}")
        print(f"Errors:   {len(errors)}")
        print(f"Warnings: {len(warnings)}")  
        print(f"Info:     {len(infos)}")
        print(f"{'='*60}\n")
        
        # Print issues by file
        files_with_issues = sorted(set(i.file for i in self.issues))
        for file in files_with_issues:
            file_issues = [i for i in self.issues if i.file == file]
            print(f"\n📄 {file}")
            for issue in sorted(file_issues, key=lambda x: x.line):
                icon = {"error": "❌", "warning": "⚠️", "info": "ℹ️"}[issue.severity]
                if issue.line > 0:
                    print(f"  {icon} Line {issue.line}: {issue.description}")
                else:
                    print(f"  {icon} {issue.description}")
        
        # Return non-zero if errors
        return 1 if errors else 0

if __name__ == "__main__":
    linter = ProofLinter(os.getcwd())
    sys.exit(linter.run()) 