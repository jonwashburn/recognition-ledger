#!/usr/bin/env python3
"""
Fix Common Issues in Lean Files

Automatically fixes:
1. Unauthorized axioms (suggests importing PhysicalPostulates)
2. Scientific notation (converts to rational form)
3. Missing imports
"""

import os
import re
from pathlib import Path
from typing import List, Tuple

class IssueFixer:
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.formal_dir = self.root_dir / "formal"
        self.fixes_applied = 0
        
    def fix_scientific_notation(self, content: str) -> str:
        """Convert scientific notation to rational form."""
        # Pattern for scientific notation: 1.23e-45 or 1.23e45
        pattern = re.compile(r'(\d+\.?\d*)[eE]([+-]?\d+)')
        
        def replace_scientific(match):
            mantissa = match.group(1)
            exponent = int(match.group(2))
            
            # Remove decimal point and count decimal places
            if '.' in mantissa:
                parts = mantissa.split('.')
                whole = parts[0]
                decimal = parts[1]
                decimal_places = len(decimal)
                number = whole + decimal
            else:
                number = mantissa
                decimal_places = 0
            
            # Calculate the rational form
            if exponent >= 0:
                if decimal_places == 0:
                    return f"{number} * 10^{exponent}"
                else:
                    return f"{number} / 10^{decimal_places} * 10^{exponent}"
            else:
                total_divisor = decimal_places - exponent
                return f"{number} / 10^{total_divisor}"
        
        return pattern.sub(replace_scientific, content)
    
    def add_missing_imports(self, content: str) -> str:
        """Add imports for PhysicalPostulates if axioms are used."""
        has_axiom = bool(re.search(r'^\s*axiom\s+', content, re.MULTILINE))
        has_import = 'PhysicalPostulates' in content
        
        if has_axiom and not has_import:
            # Add import after other imports
            import_section = re.search(r'(import\s+.+\n)+', content)
            if import_section:
                end_pos = import_section.end()
                new_content = (content[:end_pos] + 
                              "import RecognitionScience.PhysicalPostulates\n" +
                              content[end_pos:])
                return new_content
            else:
                # Add at beginning
                return "import RecognitionScience.PhysicalPostulates\n\n" + content
        
        return content
    
    def comment_unauthorized_axioms(self, content: str, filepath: Path) -> str:
        """Comment out axioms outside PhysicalPostulates.lean."""
        if 'PhysicalPostulates' in str(filepath):
            return content
            
        # Find axiom declarations
        axiom_pattern = r'^(\s*)(axiom\s+.+)$'
        
        def replace_axiom(match):
            indent = match.group(1)
            axiom_line = match.group(2)
            self.fixes_applied += 1
            return f"{indent}-- FIXME: Move to PhysicalPostulates.lean or use import\n{indent}-- {axiom_line}"
        
        return re.sub(axiom_pattern, replace_axiom, content, flags=re.MULTILINE)
    
    def fix_file(self, filepath: Path) -> bool:
        """Fix issues in a single file. Returns True if changes were made."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                original_content = f.read()
        except:
            return False
            
        content = original_content
        
        # Apply fixes
        content = self.fix_scientific_notation(content)
        content = self.add_missing_imports(content)
        content = self.comment_unauthorized_axioms(content, filepath)
        
        if content != original_content:
            # Create backup
            backup_path = filepath.with_suffix(filepath.suffix + '.backup')
            with open(backup_path, 'w', encoding='utf-8') as f:
                f.write(original_content)
            
            # Write fixed content
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            
            return True
        
        return False
    
    def fix_all(self, dry_run: bool = False) -> None:
        """Fix all Lean files in the formal directory."""
        print(f"{'DRY RUN: ' if dry_run else ''}Scanning for issues...")
        
        files_fixed = 0
        
        for lean_file in self.formal_dir.rglob("*.lean"):
            if ".lake" in str(lean_file):
                continue
                
            if dry_run:
                # Just analyze, don't fix
                try:
                    with open(lean_file, 'r') as f:
                        content = f.read()
                except:
                    continue
                    
                issues = []
                if re.search(r'\d+\.?\d*[eE][+-]?\d+', content):
                    issues.append("scientific notation")
                if re.search(r'^\s*axiom\s+', content, re.MULTILINE) and 'PhysicalPostulates' not in str(lean_file):
                    issues.append("unauthorized axioms")
                    
                if issues:
                    print(f"Would fix {lean_file.relative_to(self.formal_dir)}: {', '.join(issues)}")
                    files_fixed += 1
            else:
                if self.fix_file(lean_file):
                    print(f"Fixed: {lean_file.relative_to(self.formal_dir)}")
                    files_fixed += 1
        
        print(f"\n{'Would fix' if dry_run else 'Fixed'} {files_fixed} files")
        if not dry_run and files_fixed > 0:
            print(f"Applied {self.fixes_applied} fixes")
            print("\nBackup files created with .backup extension")

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Fix common issues in Lean files')
    parser.add_argument('--dry-run', action='store_true', 
                       help='Show what would be fixed without making changes')
    parser.add_argument('--dir', default=os.getcwd(),
                       help='Root directory (default: current)')
    
    args = parser.parse_args()
    
    fixer = IssueFixer(args.dir)
    fixer.fix_all(dry_run=args.dry_run)

if __name__ == "__main__":
    main() 