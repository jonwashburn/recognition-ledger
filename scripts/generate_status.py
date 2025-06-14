#!/usr/bin/env python3
"""
Generate Status Report for Recognition Science Formalization

Produces a markdown report showing:
- Overall completion percentage
- Sorry count per file
- Axiom dependencies
- Recent progress
"""

import os
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple

class StatusGenerator:
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.formal_dir = self.root_dir / "formal"
        
    def count_sorries(self, filepath: Path) -> int:
        """Count sorry placeholders in a file."""
        try:
            with open(filepath, 'r') as f:
                content = f.read()
                # Match 'sorry' but not in comments
                sorries = re.findall(r'\bsorry\b(?![^-]*--)', content)
                return len(sorries)
        except:
            return 0
    
    def count_theorems(self, filepath: Path) -> Tuple[int, int]:
        """Count total theorems and completed theorems."""
        try:
            with open(filepath, 'r') as f:
                content = f.read()
                # Count theorem/lemma declarations
                theorems = re.findall(r'^(theorem|lemma)\s+\w+', content, re.MULTILINE)
                total = len(theorems)
                
                # Count sorries to determine incomplete
                sorries = self.count_sorries(filepath)
                completed = max(0, total - sorries)
                
                return total, completed
        except:
            return 0, 0
    
    def check_strict_mode(self, filepath: Path) -> bool:
        """Check if file has @strict tag."""
        try:
            with open(filepath, 'r') as f:
                first_lines = f.read(1000)
                return '@strict' in first_lines
        except:
            return False
    
    def get_axiom_dependencies(self, filepath: Path) -> List[str]:
        """Find which axioms from PhysicalPostulates are used."""
        axioms = []
        try:
            with open(filepath, 'r') as f:
                content = f.read()
                # Look for specific axiom names
                axiom_names = [
                    'recognition_length', 'fundamental_tick', 'coherence_quantum',
                    'voxel_size', 'eight_beat_period', 'electron_rung', 'muon_rung'
                ]
                for axiom in axiom_names:
                    if axiom in content and 'PhysicalPostulates' not in str(filepath):
                        axioms.append(axiom)
        except:
            pass
        return axioms
    
    def analyze_file(self, filepath: Path) -> Dict:
        """Analyze a single Lean file."""
        rel_path = filepath.relative_to(self.formal_dir)
        total_theorems, completed_theorems = self.count_theorems(filepath)
        
        return {
            'path': str(rel_path),
            'name': filepath.stem,
            'total_theorems': total_theorems,
            'completed_theorems': completed_theorems,
            'sorries': self.count_sorries(filepath),
            'strict_mode': self.check_strict_mode(filepath),
            'is_completed': '_COMPLETED' in filepath.name,
            'axiom_deps': self.get_axiom_dependencies(filepath),
            'size': filepath.stat().st_size
        }
    
    def generate_report(self) -> str:
        """Generate the full status report."""
        report = []
        report.append("# Recognition Science Formalization Status")
        report.append(f"\nGenerated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("\n---\n")
        
        # Analyze all Lean files
        all_files = []
        for lean_file in self.formal_dir.rglob("*.lean"):
            if ".lake" not in str(lean_file):
                all_files.append(self.analyze_file(lean_file))
        
        # Calculate statistics
        total_files = len(all_files)
        completed_files = len([f for f in all_files if f['is_completed']])
        strict_files = len([f for f in all_files if f['strict_mode']])
        total_theorems = sum(f['total_theorems'] for f in all_files)
        completed_theorems = sum(f['completed_theorems'] for f in all_files)
        total_sorries = sum(f['sorries'] for f in all_files)
        
        # Overall summary
        report.append("## 📊 Overall Summary\n")
        report.append(f"- **Total Files**: {total_files}")
        report.append(f"- **Completed Files**: {completed_files} ({100*completed_files/total_files:.1f}%)")
        report.append(f"- **Strict Mode Files**: {strict_files}")
        report.append(f"- **Total Theorems**: {total_theorems}")
        report.append(f"- **Completed Theorems**: {completed_theorems} ({100*completed_theorems/max(1,total_theorems):.1f}%)")
        report.append(f"- **Remaining Sorries**: {total_sorries}")
        
        # Progress bar
        progress = completed_theorems / max(1, total_theorems)
        bar_length = 30
        filled = int(bar_length * progress)
        bar = '█' * filled + '░' * (bar_length - filled)
        report.append(f"\n**Progress**: [{bar}] {progress*100:.1f}%\n")
        
        # File-by-file breakdown
        report.append("## 📁 File Status\n")
        report.append("| File | Theorems | Completed | Sorries | Strict | Axioms |")
        report.append("|------|----------|-----------|---------|---------|---------|")
        
        # Sort by directory then name
        all_files.sort(key=lambda x: x['path'])
        
        for f in all_files:
            checkmark = "✅" if f['is_completed'] else "⚠️"
            strict = "✓" if f['strict_mode'] else "-"
            axioms = len(f['axiom_deps'])
            axiom_str = str(axioms) if axioms > 0 else "-"
            
            report.append(f"| {checkmark} {f['name']} | {f['total_theorems']} | "
                         f"{f['completed_theorems']} | {f['sorries']} | {strict} | {axiom_str} |")
        
        # Critical issues
        report.append("\n## 🚨 Critical Issues\n")
        
        high_sorry_files = [f for f in all_files if f['sorries'] > 5]
        if high_sorry_files:
            report.append("### Files with >5 sorries:")
            for f in sorted(high_sorry_files, key=lambda x: x['sorries'], reverse=True):
                report.append(f"- {f['path']}: {f['sorries']} sorries")
        else:
            report.append("✅ No files with excessive sorries")
        
        # Axiom dependencies
        report.append("\n## 🔗 Axiom Dependencies\n")
        axiom_usage = {}
        for f in all_files:
            for axiom in f['axiom_deps']:
                if axiom not in axiom_usage:
                    axiom_usage[axiom] = []
                axiom_usage[axiom].append(f['name'])
        
        if axiom_usage:
            for axiom, files in sorted(axiom_usage.items()):
                report.append(f"- **{axiom}**: used in {len(files)} files")
        else:
            report.append("✅ Minimal axiom dependencies")
        
        # Recommendations
        report.append("\n## 💡 Recommendations\n")
        
        # Files that should have strict mode
        should_be_strict = [f for f in all_files 
                           if f['is_completed'] and not f['strict_mode']]
        if should_be_strict:
            report.append("1. Add @strict tag to completed files:")
            for f in should_be_strict[:3]:
                report.append(f"   - {f['path']}")
        
        # Files ready for completion
        nearly_complete = [f for f in all_files 
                          if not f['is_completed'] and f['sorries'] <= 2]
        if nearly_complete:
            report.append("\n2. Files close to completion (≤2 sorries):")
            for f in nearly_complete[:3]:
                report.append(f"   - {f['path']} ({f['sorries']} sorries)")
        
        # Next steps
        report.append("\n## 🎯 Next Steps\n")
        report.append("1. Complete proofs in high-priority files")
        report.append("2. Add @strict tags to verified files")
        report.append("3. Minimize axiom dependencies")
        report.append("4. Document physical assumptions clearly")
        
        return '\n'.join(report)
    
    def save_report(self, output_path: str = None):
        """Save report to file or stdout."""
        report = self.generate_report()
        if output_path:
            with open(output_path, 'w') as f:
                f.write(report)
        else:
            print(report)

if __name__ == "__main__":
    generator = StatusGenerator(os.getcwd())
    generator.save_report()  # Prints to stdout for CI 