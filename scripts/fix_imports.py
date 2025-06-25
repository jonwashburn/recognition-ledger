#!/usr/bin/env python3
"""
Fix imports in formal/ directory to use foundation modules
"""

import os
import re
from pathlib import Path

def fix_imports_in_file(filepath):
    """Update imports in a single file"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    original_content = content
    
    # Replace RecognitionScience.axioms with foundation.RecognitionScience
    content = re.sub(
        r'import\s+RecognitionScience\.axioms',
        'import foundation.RecognitionScience',
        content
    )
    
    # Replace other RecognitionScience imports if they exist
    content = re.sub(
        r'import\s+RecognitionScience\.(\w+)',
        r'import foundation.RecognitionScience.\1',
        content
    )
    
    # If file changed, write it back
    if content != original_content:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False

def main():
    """Fix all imports in the recognition-ledger directory"""
    root_dir = Path(__file__).parent.parent
    
    # Directories to process
    dirs_to_process = ['formal', 'physics', 'ethics', 'ledger']
    
    updated_files = []
    
    for dir_name in dirs_to_process:
        dir_path = root_dir / dir_name
        if not dir_path.exists():
            print(f"Directory {dir_path} does not exist, skipping...")
            continue
            
        for lean_file in dir_path.rglob('*.lean'):
            if fix_imports_in_file(lean_file):
                updated_files.append(lean_file)
                print(f"Updated: {lean_file.relative_to(root_dir)}")
    
    print(f"\nTotal files updated: {len(updated_files)}")

if __name__ == "__main__":
    main() 