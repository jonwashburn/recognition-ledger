#!/usr/bin/env python3
"""
Audit script for foundation/ module
Scans for axioms, sorrys, and circular imports
"""

import os
import re
import sys
from collections import defaultdict
from typing import Dict, List, Tuple, Set

def find_lean_files(root_dir: str) -> List[str]:
    """Find all .lean files in foundation/ (excluding archives)"""
    lean_files = []
    for root, dirs, files in os.walk(root_dir):
        # Skip archive directories
        if 'archive' in root.lower() or 'Archive' in root:
            continue
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    return sorted(lean_files)

def scan_file_for_issues(filepath: str) -> Dict[str, List[Tuple[int, str]]]:
    """Scan a file for axioms, sorrys, and imports"""
    issues = {
        'axioms': [],
        'sorrys': [],
        'imports': []
    }
    
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    for i, line in enumerate(lines, 1):
        # Check for axioms
        if re.search(r'^\s*axiom\s+', line):
            issues['axioms'].append((i, line.strip()))
        
        # Check for sorrys (but not in comments)
        if 'sorry' in line and not line.strip().startswith('--'):
            # Check if it's actually a sorry tactic/term
            if re.search(r'\bsorry\b(?!\s*--)', line):
                issues['sorrys'].append((i, line.strip()))
        
        # Track imports for circular dependency analysis
        if line.strip().startswith('import '):
            import_stmt = line.strip()
            issues['imports'].append((i, import_stmt))
    
    return issues

def analyze_circular_imports(file_imports: Dict[str, List[str]]) -> List[List[str]]:
    """Detect circular import chains"""
    def find_cycles_from(start: str, current: str, path: List[str], visited: Set[str]) -> List[List[str]]:
        if current in path:
            # Found a cycle
            cycle_start = path.index(current)
            return [path[cycle_start:] + [current]]
        
        if current in visited:
            return []
        
        visited.add(current)
        cycles = []
        
        if current in file_imports:
            for imported in file_imports[current]:
                if imported in file_imports:  # Only follow foundation imports
                    cycles.extend(find_cycles_from(start, imported, path + [current], visited))
        
        return cycles
    
    all_cycles = []
    for file in file_imports:
        cycles = find_cycles_from(file, file, [], set())
        for cycle in cycles:
            # Normalize cycle to start with smallest element
            if cycle and cycle not in all_cycles:
                min_idx = cycle.index(min(cycle))
                normalized = cycle[min_idx:] + cycle[:min_idx]
                if normalized not in all_cycles:
                    all_cycles.append(normalized)
    
    return all_cycles

def generate_markdown_report(audit_results: Dict, output_file: str):
    """Generate markdown report of audit results"""
    with open(output_file, 'w') as f:
        f.write("# Foundation Proof Ledger\n\n")
        f.write("_Generated audit of `foundation/` module for axioms, sorrys, and circular imports._\n\n")
        
        # Summary table
        f.write("## Summary\n\n")
        f.write("| Metric | Count | Status |\n")
        f.write("|--------|-------|--------|\n")
        
        total_axioms = sum(len(r['axioms']) for r in audit_results['files'].values())
        total_sorrys = sum(len(r['sorrys']) for r in audit_results['files'].values())
        total_cycles = len(audit_results['circular_imports'])
        
        f.write(f"| Axioms | {total_axioms} | {'❌' if total_axioms > 0 else '✅'} |\n")
        f.write(f"| Sorrys | {total_sorrys} | {'❌' if total_sorrys > 0 else '✅'} |\n")
        f.write(f"| Circular imports | {total_cycles} | {'❌' if total_cycles > 0 else '✅'} |\n\n")
        
        # File-by-file breakdown
        f.write("## File Analysis\n\n")
        f.write("| File | Axioms | Sorrys | Status |\n")
        f.write("|------|--------|--------|--------|\n")
        
        for filepath, issues in sorted(audit_results['files'].items()):
            rel_path = filepath.replace('foundation/', '')
            axiom_count = len(issues['axioms'])
            sorry_count = len(issues['sorrys'])
            status = '✅' if axiom_count == 0 and sorry_count == 0 else '❌'
            f.write(f"| `{rel_path}` | {axiom_count} | {sorry_count} | {status} |\n")
        
        # Detailed issues
        f.write("\n## Detailed Issues\n\n")
        
        # Axioms
        if total_axioms > 0:
            f.write("### Axioms Found\n\n")
            for filepath, issues in sorted(audit_results['files'].items()):
                if issues['axioms']:
                    rel_path = filepath.replace('foundation/', '')
                    f.write(f"**`{rel_path}`**\n")
                    for line_no, line in issues['axioms']:
                        f.write(f"- Line {line_no}: `{line}`\n")
                    f.write("\n")
        
        # Sorrys
        if total_sorrys > 0:
            f.write("### Sorrys Found\n\n")
            for filepath, issues in sorted(audit_results['files'].items()):
                if issues['sorrys']:
                    rel_path = filepath.replace('foundation/', '')
                    f.write(f"**`{rel_path}`**\n")
                    for line_no, line in issues['sorrys']:
                        f.write(f"- Line {line_no}: `{line}`\n")
                    f.write("\n")
        
        # Circular imports
        if audit_results['circular_imports']:
            f.write("### Circular Import Chains\n\n")
            for i, cycle in enumerate(audit_results['circular_imports'], 1):
                f.write(f"{i}. ")
                f.write(" → ".join(f"`{f}`" for f in cycle))
                f.write("\n")

def main():
    """Run the audit"""
    foundation_dir = 'foundation'
    
    if not os.path.exists(foundation_dir):
        print(f"Error: {foundation_dir}/ directory not found")
        sys.exit(1)
    
    print("Scanning foundation/ for issues...")
    
    # Find all Lean files
    lean_files = find_lean_files(foundation_dir)
    print(f"Found {len(lean_files)} Lean files")
    
    # Scan each file
    audit_results = {
        'files': {},
        'circular_imports': []
    }
    
    file_imports = {}  # Map from file to its foundation imports
    
    for filepath in lean_files:
        rel_path = os.path.relpath(filepath, foundation_dir)
        issues = scan_file_for_issues(filepath)
        audit_results['files'][filepath] = issues
        
        # Extract foundation imports for circular dependency check
        foundation_imports = []
        for _, import_line in issues['imports']:
            match = re.match(r'import\s+(foundation\.\S+)', import_line)
            if match:
                # Convert import to file path
                import_path = match.group(1).replace('.', '/') + '.lean'
                foundation_imports.append(import_path)
        
        file_imports[rel_path] = foundation_imports
    
    # Check for circular imports
    print("Analyzing import dependencies...")
    circular_chains = analyze_circular_imports(file_imports)
    audit_results['circular_imports'] = circular_chains
    
    # Generate report
    output_file = 'docs/Foundation_Proof_Ledger.md'
    os.makedirs('docs', exist_ok=True)
    generate_markdown_report(audit_results, output_file)
    print(f"\nGenerated report: {output_file}")
    
    # Summary
    total_axioms = sum(len(r['axioms']) for r in audit_results['files'].values())
    total_sorrys = sum(len(r['sorrys']) for r in audit_results['files'].values())
    total_cycles = len(circular_chains)
    
    print(f"\nAudit Summary:")
    print(f"  Axioms found: {total_axioms}")
    print(f"  Sorrys found: {total_sorrys}")
    print(f"  Circular import chains: {total_cycles}")
    
    # Exit with error if any issues found
    if total_axioms > 0 or total_sorrys > 0 or total_cycles > 0:
        print("\n❌ Foundation has issues that need to be resolved")
        sys.exit(1)
    else:
        print("\n✅ Foundation is clean!")
        sys.exit(0)

if __name__ == '__main__':
    main() 