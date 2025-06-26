#!/usr/bin/env python3
"""
Tactic Filter - Try built-in tactics before calling LLM
"""

import subprocess
import tempfile
from pathlib import Path
from typing import Optional, List, Tuple
import asyncio
import concurrent.futures

class TacticFilter:
    def __init__(self, timeout_ms: int = 300):
        self.timeout_ms = timeout_ms
        self.simple_tactics = [
            "rfl",
            "simp",
            "simp [*]",
            "aesop",
            "norm_num",
            "ring",
            "field_simp",
            "linarith",
            "omega",
            "decide",
            "trivial",
            "exact trivial",
            "constructor",
            "intro; rfl",
            "intro; simp",
            "intro; aesop",
            "intros; rfl",
            "intros; simp",
            "intros; aesop",
            "cases h; rfl",
            "cases h; simp",
            "ext; simp",
            "ext; rfl",
            "unfold_let; simp",
            "unfold_let; rfl",
            "simp only [*]",
            "simp [*, -mul_comm]",
            "simp [h]",
            "rw [h]; rfl",
            "rw [←h]; rfl",
            "apply And.intro <;> simp",
            "constructor <;> simp",
            "constructor <;> intro <;> simp"
        ]
        
    async def try_simple_tactics(self, file_path: Path, sorry_line: int,
                                theorem_name: str) -> Optional[str]:
        """
        Try simple tactics on a sorry
        Returns the first working tactic or None
        """
        # Read file content
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Try tactics in parallel
        tasks = []
        for tactic in self.simple_tactics:
            task = self._try_single_tactic(file_path, sorry_line, tactic, content)
            tasks.append(task)
            
        # Wait for first success or all failures
        for coro in asyncio.as_completed(tasks):
            result = await coro
            if result:
                # Cancel remaining tasks
                for task in tasks:
                    if not task.done():
                        task.cancel()
                return result
                
        return None
        
    async def _try_single_tactic(self, file_path: Path, sorry_line: int,
                                 tactic: str, original_content: str) -> Optional[str]:
        """
        Try a single tactic
        """
        try:
            # Create temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as tmp:
                lines = original_content.split('\n')
                
                # Replace sorry with tactic
                if sorry_line <= len(lines):
                    line = lines[sorry_line - 1]
                    
                    if 'by sorry' in line:
                        new_line = line.replace('by sorry', f'by {tactic}')
                    elif ' sorry' in line:
                        new_line = line.replace(' sorry', f' by {tactic}')
                    else:
                        # Can't easily apply tactic mode
                        return None
                        
                    lines[sorry_line - 1] = new_line
                    tmp.write('\n'.join(lines))
                    tmp_path = Path(tmp.name)
                    
            # Try to compile with timeout
            result = await self._compile_with_timeout(tmp_path)
            
            # Clean up
            try:
                tmp_path.unlink()
            except:
                pass
                
            if result:
                return f"by {tactic}"
                
        except Exception:
            pass
            
        return None
        
    async def _compile_with_timeout(self, file_path: Path) -> bool:
        """
        Compile with timeout
        """
        try:
            # Find project root
            project_root = file_path.parent
            while project_root.parent != project_root:
                if (project_root / "lakefile.lean").exists():
                    break
                project_root = project_root.parent
                    
            # Run lake env lean (faster than lake build)
            proc = await asyncio.create_subprocess_exec(
                'lake', 'env', 'lean', str(file_path),
                cwd=str(project_root),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            
            try:
                stdout, stderr = await asyncio.wait_for(
                    proc.communicate(),
                    timeout=self.timeout_ms / 1000.0
                )
                return proc.returncode == 0
            except asyncio.TimeoutError:
                proc.kill()
                return False
                
        except Exception:
            return False
            
    def get_tactic_suggestions(self, goal_type: str) -> List[str]:
        """
        Get tactic suggestions based on goal type
        """
        suggestions = []
        
        # Equality goals
        if '=' in goal_type:
            suggestions.extend(['rfl', 'simp', 'ring', 'field_simp', 'norm_num'])
            
        # Inequality goals  
        if any(op in goal_type for op in ['<', '>', '≤', '≥', '≠']):
            suggestions.extend(['linarith', 'norm_num', 'simp', 'omega'])
            
        # Logic goals
        if any(op in goal_type for op in ['∧', '∨', '→', '↔', '¬']):
            suggestions.extend(['aesop', 'simp', 'tauto', 'decide'])
            
        # Membership goals
        if '∈' in goal_type:
            suggestions.extend(['simp', 'aesop', 'simp [Set.mem_def]'])
            
        # Natural number goals
        if 'Nat' in goal_type or 'ℕ' in goal_type:
            suggestions.extend(['omega', 'norm_num', 'simp', 'induction'])
            
        # Real number goals
        if 'Real' in goal_type or 'ℝ' in goal_type:
            suggestions.extend(['norm_num', 'field_simp', 'linarith', 'ring'])
            
        return suggestions 