#!/usr/bin/env python3
"""
Recognition Science Autonomous Solver Package Overview
=====================================================

This script provides an overview of the Recognition Science solver ecosystem.
"""

import os
import glob

def print_package_structure():
    """Display the package structure"""
    print("🌌 Recognition Science Autonomous Solver Package")
    print("=" * 50)
    print()
    
    # Lean configuration
    print("📦 Lean 4 Configuration:")
    print("  • Lean version: 4.11.0")
    print("  • Package name: RecognitionScience")
    print("  • Main executable: recognition-solver")
    print()
    
    # Python solvers
    print("🤖 Autonomous Solvers (all using Claude Sonnet 4):")
    solvers = [
        ("ultimate_autonomous_solver.py", "20 parallel agents, 30KB powerhouse"),
        ("claude_sonnet_enhanced_solver.py", "Enhanced solver (renamed from o3)"),
        ("zero_sorry_solver.py", "Completes all 'sorry' proofs"),
        ("unified_completion_solver.py", "Unified completion system"),
        ("mass_proof_generator.py", "Batch proof generation"),
        ("advanced_proof_solver.py", "Advanced proof tactics"),
    ]
    
    for solver, desc in solvers:
        if os.path.exists(f"formal/{solver}"):
            print(f"  ✓ {solver}")
            print(f"    └─ {desc}")
        else:
            print(f"  ? {solver} (not found)")
    print()
    
    # Lean modules
    print("📚 Lean Modules:")
    modules = [
        ("RecognitionScience.lean", "Main module with core definitions"),
        ("Main.lean", "Executable entry point"),
        ("formal/axioms.lean", "8 fundamental axioms"),
        ("formal/Core/GoldenRatio.lean", "φ emergence proofs"),
        ("formal/Physics/MassCascade.lean", "Particle mass derivations"),
        ("formal/Physics/CoherenceQuantum.lean", "E_coh = 0.090 eV proofs"),
    ]
    
    for module, desc in modules:
        if os.path.exists(module):
            print(f"  ✓ {module}")
            print(f"    └─ {desc}")
        else:
            print(f"  ? {module} (needs creation)")
    print()
    
    # Count Python files
    python_files = glob.glob("formal/*.py")
    lean_files = glob.glob("formal/*.lean")
    
    print("📊 Statistics:")
    print(f"  • Total Python solvers: {len(python_files)}")
    print(f"  • Total Lean files in formal/: {len(lean_files)}")
    print(f"  • Unique solver approach: Claude Sonnet 4 exclusively")
    print()
    
    print("🚀 To run the solvers:")
    print("  1. Set ANTHROPIC_API_KEY environment variable")
    print("  2. Run: python3 formal/ultimate_autonomous_solver.py")
    print("  3. Or use: ./run_solvers.sh for interactive menu")

if __name__ == "__main__":
    print_package_structure() 