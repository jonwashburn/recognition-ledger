#!/usr/bin/env python3
"""
Focused solver for AxiomProofs.lean recognition_fixed_points_corrected proofs
"""

from pathlib import Path
import sys
sys.path.append(str(Path(__file__).parent))

from navier_stokes_rs_solver_o3 import EightBeatSolver

def main():
    print("🎯 Targeting AxiomProofs.lean - recognition_fixed_points_corrected")
    print("=" * 60)
    
    solver = EightBeatSolver(Path.cwd())
    
    # Target AxiomProofs.lean
    target = Path("formal/AxiomProofs.lean")
    if target.exists():
        print(f"\n📄 Processing {target}")
        print("   Focus: recognition_fixed_points_corrected theorems")
        print("   These appear to be related to golden ratio properties")
        print()
        
        # Run solver on just the first few to test
        results = solver.solve_file(target)
        
        success = sum(1 for v in results.values() if v)
        total = len(results)
        
        print(f"\n📊 Results: {success}/{total} proofs completed")
        
        if success > 0:
            print(f"   Success rate: {success/total*100:.1f}%")
            print("\n✅ Some proofs were successful!")
            print("   Check formal/AxiomProofs.lean for updates")
        else:
            print("\n❌ No proofs completed successfully")
            print("   This might require more specialized tactics")
    else:
        print(f"❌ File not found: {target}")

if __name__ == "__main__":
    main() 