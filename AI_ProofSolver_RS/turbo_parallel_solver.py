#!/usr/bin/env python3
"""
Turbo Parallel Solver - Integrates all performance improvements
"""

import os
import asyncio
import anthropic
from pathlib import Path
from typing import List, Dict, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed
import time
import json

from proof_cache import ProofCache
from compile_checker import CompileChecker
from context_extractor import ContextExtractor
from tactic_filter import TacticFilter
from enhanced_prompt_system import EnhancedPromptSystem

class TurboParallelSolver:
    def __init__(self, api_key: str, max_workers: int = 4):
        self.api_key = api_key
        self.max_workers = max_workers
        
        # Components
        self.cache = ProofCache()
        self.compiler = CompileChecker()
        self.extractor = ContextExtractor()
        self.tactic_filter = TacticFilter(timeout_ms=300)
        self.prompt_system = EnhancedPromptSystem()
        
        # Create a pool of clients
        self.clients = [anthropic.Anthropic(api_key=api_key) for _ in range(max_workers)]
        self.model = "claude-opus-4-20250514"
        
        # Thread pool for parallel execution
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        
        # Statistics
        self.stats = {
            'cache_hits': 0,
            'tactic_filter_hits': 0,
            'llm_successes': 0,
            'total_attempts': 0
        }
        
    async def solve_sorry_worker(self, worker_id: int, file_path: Path, 
                                sorry_info: Dict) -> Tuple[str, Optional[str], Dict]:
        """Enhanced worker with all improvements"""
        sorry_name = sorry_info['name']
        stats = {'method': None, 'attempts': 0, 'time': 0}
        start_time = time.time()
        
        self.stats['total_attempts'] += 1
        
        # 1. Check cache first
        cached_proof = self.cache.lookup_proof(sorry_info['declaration'])
        if cached_proof:
            success, error = self.compiler.check_proof(
                file_path, sorry_info['line'], cached_proof
            )
            if success:
                self.stats['cache_hits'] += 1
                stats['method'] = 'cache'
                stats['time'] = time.time() - start_time
                return (sorry_name, cached_proof, stats)
                
        # 2. Try simple tactics first
        simple_proof = await self.tactic_filter.try_simple_tactics(
            file_path, sorry_info['line'], sorry_name
        )
        if simple_proof:
            self.stats['tactic_filter_hits'] += 1
            self.cache.store_proof(sorry_info['declaration'], simple_proof, True)
            stats['method'] = 'tactic_filter'
            stats['time'] = time.time() - start_time
            return (sorry_name, simple_proof, stats)
            
        # 3. Extract context and prepare for LLM
        context = self.extractor.extract_context(file_path, sorry_info['line'])
        
        # 4. Multi-shot LLM approach
        prompts = self.prompt_system.create_multi_shot_prompts(
            sorry_name, 
            sorry_info.get('type', sorry_info['declaration']),
            context
        )
        
        # Try prompts in parallel
        client = self.clients[worker_id]
        proof = await self._try_prompts_parallel(
            client, prompts, file_path, sorry_info, stats
        )
        
        if proof:
            self.stats['llm_successes'] += 1
            self.cache.store_proof(sorry_info['declaration'], proof, True)
            stats['method'] = 'llm'
            
        stats['time'] = time.time() - start_time
        return (sorry_name, proof, stats)
        
    async def _try_prompts_parallel(self, client, prompts: List[str], 
                                   file_path: Path, sorry_info: Dict,
                                   stats: Dict) -> Optional[str]:
        """Try multiple prompts in parallel"""
        tasks = []
        
        for i, prompt in enumerate(prompts):
            task = asyncio.create_task(
                self._try_single_prompt(client, prompt, file_path, sorry_info, i)
            )
            tasks.append(task)
            
        # Wait for first success
        for coro in asyncio.as_completed(tasks):
            result = await coro
            if result:
                # Cancel remaining tasks
                for task in tasks:
                    if not task.done():
                        task.cancel()
                stats['attempts'] = len(prompts)
                return result
                
        stats['attempts'] = len(prompts)
        return None
        
    async def _try_single_prompt(self, client, prompt: str, file_path: Path,
                                sorry_info: Dict, prompt_id: int) -> Optional[str]:
        """Try a single prompt with compilation check"""
        try:
            # Use asyncio for non-blocking API call
            loop = asyncio.get_event_loop()
            response = await loop.run_in_executor(
                None,
                lambda: client.messages.create(
                    model=self.model,
                    max_tokens=500,
                    temperature=0.1 if prompt_id == 0 else 0.3,
                    messages=[{"role": "user", "content": prompt}]
                )
            )
            
            proof = response.content[0].text.strip()
            if proof.startswith('```'):
                lines = proof.split('\n')
                proof = '\n'.join(lines[1:-1])
                
            # Quick syntax check
            syntax_ok, _ = self.compiler.validate_syntax(proof)
            if not syntax_ok:
                return None
                
            # Compile check
            success, _ = self.compiler.check_proof(
                file_path, sorry_info['line'], proof
            )
            
            return proof if success else None
            
        except Exception:
            return None
            
    async def solve_file_async(self, file_path: Path, max_proofs: int = 20):
        """Solve sorries with maximum parallelism"""
        print(f"\n{'='*60}")
        print(f"TURBO Parallel Solver: {file_path}")
        print(f"Workers: {self.max_workers}")
        print('='*60)
        
        # Find sorries
        sorries = self.find_sorries(file_path)
        if not sorries:
            print("No sorries found!")
            return
            
        print(f"Found {len(sorries)} sorries")
        
        # Sort by estimated difficulty (smaller goals first)
        sorries.sort(key=lambda s: len(s['declaration']))
        
        sorries_to_process = sorries[:max_proofs]
        
        # Process all in parallel
        start_time = time.time()
        tasks = []
        
        for i, sorry_info in enumerate(sorries_to_process):
            worker_id = i % self.max_workers
            task = asyncio.create_task(
                self.solve_sorry_worker(worker_id, file_path, sorry_info)
            )
            tasks.append(task)
            
        # Gather results
        results = await asyncio.gather(*tasks)
        
        # Display results
        print("\nResults:")
        resolved = 0
        for sorry_name, proof, stats in results:
            if proof:
                resolved += 1
                print(f"  ✓ {sorry_name}: {stats['method']} ({stats['time']:.2f}s)")
            else:
                print(f"  ✗ {sorry_name}: Failed after {stats['attempts']} attempts")
                
        # Summary
        elapsed = time.time() - start_time
        
        print(f"\n{'='*60}")
        print(f"Completed in {elapsed:.1f} seconds")
        print(f"Resolved: {resolved}/{len(sorries_to_process)}")
        print(f"Speed: {len(sorries_to_process)/elapsed:.1f} sorries/second")
        
        # Detailed stats
        print(f"\nPerformance breakdown:")
        print(f"  Cache hits: {self.stats['cache_hits']}")
        print(f"  Tactic filter: {self.stats['tactic_filter_hits']}")
        print(f"  LLM successes: {self.stats['llm_successes']}")
        
        cache_stats = self.cache.get_statistics()
        print(f"\nCache efficiency:")
        print(f"  Total cached: {cache_stats['total_cached']}")
        print(f"  Hit rate: {cache_stats['hit_rate']:.1%}")
        
    def find_sorries(self, file_path: Path) -> List[Dict]:
        """Find all sorries in a file"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        sorries = []
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Extract theorem name
                j = i
                while j > 0 and not any(kw in lines[j] for kw in ['theorem ', 'lemma ', 'def ']):
                    j -= 1
                    
                if j >= 0:
                    decl_line = lines[j]
                    name_match = None
                    for kw in ['theorem ', 'lemma ', 'def ']:
                        if kw in decl_line:
                            parts = decl_line.split(kw)[1].split()
                            if parts:
                                name_match = parts[0].rstrip(':')
                                break
                                
                    if name_match:
                        # Get full declaration
                        decl_lines = []
                        k = j
                        while k < len(lines) and ':=' not in lines[k]:
                            decl_lines.append(lines[k].strip())
                            k += 1
                        declaration = ' '.join(decl_lines)
                        
                        sorries.append({
                            'name': name_match,
                            'line': i + 1,
                            'declaration': declaration
                        })
                        
        return sorries
        
    def solve_file(self, file_path: Path, max_proofs: int = 20):
        """Synchronous wrapper"""
        asyncio.run(self.solve_file_async(file_path, max_proofs))
        
def main():
    api_key = os.getenv('ANTHROPIC_API_KEY')
    if not api_key:
        print("Please set ANTHROPIC_API_KEY environment variable")
        return
        
    solver = TurboParallelSolver(api_key, max_workers=4)
    
    # Test on high-value targets
    test_files = [
        Path("../formal/AxiomProofs.lean"),
        Path("../formal/MetaPrinciple.lean"),
        Path("../formal/Core/GoldenRatio.lean"),
    ]
    
    for file_path in test_files:
        if file_path.exists():
            solver.solve_file(file_path)
            
if __name__ == "__main__":
    main() 