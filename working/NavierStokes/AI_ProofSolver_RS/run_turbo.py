#!/usr/bin/env python3
"""
Run the Turbo Parallel Solver on all Recognition Science files
"""

import os
import sys
from pathlib import Path
import time

# Add current directory to path
sys.path.insert(0, str(Path(__file__).parent))

from turbo_parallel_solver import TurboParallelSolver

def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    # High-priority files with most sorries
    priority_files = [
        "../formal/AxiomProofs.lean",
        "../formal/MetaPrinciple.lean", 
        "../formal/Core/GoldenRatio.lean",
        "../formal/Core/EightBeat.lean",
        "../formal/Numerics/DecimalTactics.lean",
        "../formal/DetailedProofs.lean",
        "../formal/RecognitionTheorems.lean",
        "../formal/Numerics/ErrorBounds.lean",
        "../formal/FundamentalTick.lean",
        "../formal/Journal/Predictions.lean",
        "../formal/RG/Yukawa.lean",
        "../formal/Variational.lean",
        "../formal/EightTickWeinberg.lean",
        "../formal/NumericalTactics.lean",
    ]
    
    # Additional files
    other_files = [
        "../formal/Philosophy/Death.lean",
        "../formal/Philosophy/Purpose.lean",
        "../formal/Philosophy/Ethics.lean",
        "../formal/ParticleMassesRevised.lean",
        "../formal/NumericalVerification.lean",
        "../formal/GravitationalConstant.lean",
        "../formal/ElectroweakTheory.lean",
        "../formal/Dimension.lean",
        "../formal/CosmologicalPredictions.lean",
        "../formal/CoherenceQuantum.lean",
        "../formal/NumericalTests.lean",
        "../formal/ScaleConsistency.lean",
        "../formal/QCDConfinement.lean",
    ]
    
    print("="*80)
    print("TURBO PARALLEL SOLVER - Recognition Science")
    print("="*80)
    
    solver = TurboParallelSolver(api_key, max_workers=4)
    
    overall_start = time.time()
    total_resolved = 0
    total_attempted = 0
    
    # Process priority files first
    print("\nProcessing high-priority files...")
    for file_path in priority_files:
        path = Path(file_path)
        if path.exists():
            # Reset per-file stats
            solver.stats = {
                'cache_hits': 0,
                'tactic_filter_hits': 0,
                'llm_successes': 0,
                'total_attempts': 0
            }
            solver.solve_file(path, max_proofs=20)
            
            # Track totals
            total_attempted += solver.stats['total_attempts']
            total_resolved += (solver.stats['cache_hits'] + 
                             solver.stats['tactic_filter_hits'] + 
                             solver.stats['llm_successes'])
    
    # Process other files
    print("\n\nProcessing additional files...")
    for file_path in other_files:
        path = Path(file_path)
        if path.exists():
            # Reset per-file stats
            solver.stats = {
                'cache_hits': 0,
                'tactic_filter_hits': 0,
                'llm_successes': 0,
                'total_attempts': 0
            }
            solver.solve_file(path, max_proofs=10)
            
            # Track totals
            total_attempted += solver.stats['total_attempts']
            total_resolved += (solver.stats['cache_hits'] + 
                             solver.stats['tactic_filter_hits'] + 
                             solver.stats['llm_successes'])
    
    # Final summary
    overall_time = time.time() - overall_start
    
    print("\n" + "="*80)
    print("TURBO SOLVER SESSION COMPLETE")
    print("="*80)
    print(f"Total time: {overall_time:.1f} seconds")
    print(f"Total sorries attempted: {total_attempted}")
    print(f"Total sorries resolved: {total_resolved}")
    if total_attempted > 0:
        print(f"Success rate: {total_resolved/total_attempted:.1%}")
        print(f"Average speed: {total_attempted/overall_time:.1f} sorries/second")
    
    # Cache final stats
    cache_stats = solver.cache.get_statistics()
    print(f"\nFinal cache statistics:")
    print(f"  Total cached proofs: {cache_stats['total_cached']}")
    print(f"  Overall hit rate: {cache_stats['hit_rate']:.1%}")
    
if __name__ == "__main__":
    main() 