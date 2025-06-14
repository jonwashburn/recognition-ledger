#!/usr/bin/env python3
"""
Autonomous Proof Runner - Manages large-scale autonomous proof attempts
with checkpointing, monitoring, and intelligent retry strategies
"""

import os
import json
import time
import asyncio
import logging
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from concurrent.futures import ProcessPoolExecutor
import signal
import sys
import pickle
from pathlib import Path

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('autonomous_proof.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class ProofSession:
    """Represents an autonomous proof session"""
    session_id: str
    start_time: datetime
    last_checkpoint: datetime
    total_attempts: int = 0
    successful_proofs: int = 0
    failed_proofs: int = 0
    current_targets: List[str] = None
    checkpoint_file: str = None
    
    def __post_init__(self):
        if self.current_targets is None:
            self.current_targets = []
        if self.checkpoint_file is None:
            self.checkpoint_file = f"checkpoint_{self.session_id}.pkl"

@dataclass 
class ProofTask:
    """Individual proof task with full context"""
    task_id: str
    axiom_name: str
    lemma_name: str
    statement: str
    dependencies: List[str]
    attempts: int = 0
    max_attempts: int = 5
    last_error: Optional[str] = None
    proof_code: Optional[str] = None
    is_proven: bool = False
    priority: int = 1  # Higher priority = prove first
    
class ProofMonitor:
    """Monitors proof progress and system health"""
    
    def __init__(self, max_memory_mb: int = 4096, max_time_hours: int = 24):
        self.max_memory = max_memory_mb * 1024 * 1024  # Convert to bytes
        self.max_time = timedelta(hours=max_time_hours)
        self.start_time = datetime.now()
        self.metrics = {
            "proofs_per_hour": [],
            "memory_usage": [],
            "active_tasks": []
        }
    
    def check_resources(self) -> Tuple[bool, str]:
        """Check if we should continue running"""
        # Check time limit
        if datetime.now() - self.start_time > self.max_time:
            return False, "Time limit exceeded"
        
        # Check memory usage (simplified - would use psutil in practice)
        try:
            import resource
            usage = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            if usage > self.max_memory:
                return False, f"Memory limit exceeded: {usage / 1024 / 1024:.2f} MB"
        except:
            pass
        
        return True, "OK"
    
    def record_proof_attempt(self, task: ProofTask, success: bool):
        """Record metrics for a proof attempt"""
        hour = int((datetime.now() - self.start_time).total_seconds() / 3600)
        if hour >= len(self.metrics["proofs_per_hour"]):
            self.metrics["proofs_per_hour"].extend([0] * (hour + 1 - len(self.metrics["proofs_per_hour"])))
        
        if success:
            self.metrics["proofs_per_hour"][hour] += 1
    
    def get_performance_summary(self) -> Dict:
        """Get performance metrics"""
        total_proofs = sum(self.metrics["proofs_per_hour"])
        runtime = (datetime.now() - self.start_time).total_seconds() / 3600
        
        return {
            "total_proofs": total_proofs,
            "runtime_hours": runtime,
            "average_proofs_per_hour": total_proofs / max(1, runtime),
            "peak_proofs_per_hour": max(self.metrics["proofs_per_hour"]) if self.metrics["proofs_per_hour"] else 0
        }

class AdaptiveProofStrategy:
    """Adapts proof strategies based on success patterns"""
    
    def __init__(self):
        self.strategy_success = {
            "simp_first": {"attempts": 0, "successes": 0},
            "case_split": {"attempts": 0, "successes": 0},
            "induction": {"attempts": 0, "successes": 0},
            "contradiction": {"attempts": 0, "successes": 0},
            "calculation": {"attempts": 0, "successes": 0},
            "mathlib_search": {"attempts": 0, "successes": 0}
        }
        self.lemma_patterns = {}  # Track which strategies work for which lemma types
    
    def record_attempt(self, task: ProofTask, strategy: str, success: bool):
        """Record the outcome of a proof attempt"""
        if strategy in self.strategy_success:
            self.strategy_success[strategy]["attempts"] += 1
            if success:
                self.strategy_success[strategy]["successes"] += 1
        
        # Track patterns
        lemma_type = self._classify_lemma(task.statement)
        if lemma_type not in self.lemma_patterns:
            self.lemma_patterns[lemma_type] = {}
        if strategy not in self.lemma_patterns[lemma_type]:
            self.lemma_patterns[lemma_type][strategy] = {"attempts": 0, "successes": 0}
        
        self.lemma_patterns[lemma_type][strategy]["attempts"] += 1
        if success:
            self.lemma_patterns[lemma_type][strategy]["successes"] += 1
    
    def _classify_lemma(self, statement: str) -> str:
        """Classify lemma type based on statement"""
        statement_lower = statement.lower()
        
        if "converge" in statement_lower or "summable" in statement_lower:
            return "convergence"
        elif "continuous" in statement_lower or "bounded" in statement_lower:
            return "continuity"
        elif "=" in statement and not "≠" in statement:
            return "equality"
        elif "∀" in statement or "forall" in statement_lower:
            return "universal"
        elif "∃" in statement or "exists" in statement_lower:
            return "existential"
        else:
            return "general"
    
    def get_best_strategies(self, task: ProofTask, n: int = 3) -> List[str]:
        """Get the n best strategies for a given task"""
        lemma_type = self._classify_lemma(task.statement)
        
        # Calculate success rates
        strategy_scores = []
        
        # Global success rates
        for strategy, stats in self.strategy_success.items():
            if stats["attempts"] > 0:
                global_rate = stats["successes"] / stats["attempts"]
            else:
                global_rate = 0.1  # Default rate for untried strategies
            
            # Specific success rate for this lemma type
            if lemma_type in self.lemma_patterns and strategy in self.lemma_patterns[lemma_type]:
                specific_stats = self.lemma_patterns[lemma_type][strategy]
                if specific_stats["attempts"] > 0:
                    specific_rate = specific_stats["successes"] / specific_stats["attempts"]
                else:
                    specific_rate = global_rate
            else:
                specific_rate = global_rate
            
            # Weighted average (favor specific patterns as we get more data)
            weight = min(0.8, task.attempts * 0.2)
            score = weight * specific_rate + (1 - weight) * global_rate
            
            # Boost strategies we haven't tried much for this task
            if task.attempts < 3:
                score *= 1.2
            
            strategy_scores.append((strategy, score))
        
        # Sort by score and return top n
        strategy_scores.sort(key=lambda x: x[1], reverse=True)
        return [s[0] for s in strategy_scores[:n]]

class AutonomousProofRunner:
    """Main runner for autonomous proof sessions"""
    
    def __init__(self, api_key: str, checkpoint_dir: str = "checkpoints"):
        self.api_key = api_key
        self.checkpoint_dir = Path(checkpoint_dir)
        self.checkpoint_dir.mkdir(exist_ok=True)
        self.monitor = ProofMonitor()
        self.strategy = AdaptiveProofStrategy()
        self.session: Optional[ProofSession] = None
        self.task_queue: List[ProofTask] = []
        self.completed_tasks: Dict[str, ProofTask] = {}
        
        # Setup signal handlers for graceful shutdown
        signal.signal(signal.SIGINT, self._handle_shutdown)
        signal.signal(signal.SIGTERM, self._handle_shutdown)
    
    def _handle_shutdown(self, signum, frame):
        """Handle graceful shutdown"""
        logger.info("Received shutdown signal, saving checkpoint...")
        self.save_checkpoint()
        logger.info("Checkpoint saved. Exiting.")
        sys.exit(0)
    
    def save_checkpoint(self):
        """Save current state to checkpoint file"""
        if not self.session:
            return
        
        checkpoint = {
            "session": asdict(self.session),
            "task_queue": [asdict(t) for t in self.task_queue],
            "completed_tasks": {k: asdict(v) for k, v in self.completed_tasks.items()},
            "strategy_state": {
                "success_rates": self.strategy.strategy_success,
                "patterns": self.strategy.lemma_patterns
            },
            "monitor_metrics": self.monitor.metrics
        }
        
        checkpoint_path = self.checkpoint_dir / self.session.checkpoint_file
        with open(checkpoint_path, 'wb') as f:
            pickle.dump(checkpoint, f)
        
        logger.info(f"Checkpoint saved to {checkpoint_path}")
    
    def load_checkpoint(self, checkpoint_file: str) -> bool:
        """Load state from checkpoint file"""
        checkpoint_path = self.checkpoint_dir / checkpoint_file
        if not checkpoint_path.exists():
            return False
        
        try:
            with open(checkpoint_path, 'rb') as f:
                checkpoint = pickle.load(f)
            
            # Restore session
            self.session = ProofSession(**checkpoint["session"])
            
            # Restore task queue
            self.task_queue = [ProofTask(**t) for t in checkpoint["task_queue"]]
            
            # Restore completed tasks
            self.completed_tasks = {k: ProofTask(**v) for k, v in checkpoint["completed_tasks"].items()}
            
            # Restore strategy state
            self.strategy.strategy_success = checkpoint["strategy_state"]["success_rates"]
            self.strategy.lemma_patterns = checkpoint["strategy_state"]["patterns"]
            
            # Restore monitor metrics
            self.monitor.metrics = checkpoint["monitor_metrics"]
            
            logger.info(f"Checkpoint loaded from {checkpoint_path}")
            return True
            
        except Exception as e:
            logger.error(f"Failed to load checkpoint: {e}")
            return False
    
    async def run_proof_session(self, targets: List[str], session_id: Optional[str] = None,
                               resume_from_checkpoint: Optional[str] = None):
        """Run an autonomous proof session"""
        
        # Initialize or resume session
        if resume_from_checkpoint and self.load_checkpoint(resume_from_checkpoint):
            logger.info(f"Resuming session {self.session.session_id}")
        else:
            self.session = ProofSession(
                session_id=session_id or datetime.now().strftime("%Y%m%d_%H%M%S"),
                start_time=datetime.now(),
                last_checkpoint=datetime.now(),
                current_targets=targets
            )
            
            # Initialize task queue
            await self._initialize_tasks(targets)
        
        logger.info(f"Starting proof session {self.session.session_id}")
        logger.info(f"Tasks in queue: {len(self.task_queue)}")
        
        # Main proof loop
        while self.task_queue:
            # Check resources
            can_continue, reason = self.monitor.check_resources()
            if not can_continue:
                logger.warning(f"Stopping session: {reason}")
                break
            
            # Get next batch of tasks
            batch = self._get_next_batch(batch_size=5)
            
            # Process batch in parallel
            results = await self._process_batch_parallel(batch)
            
            # Update queue and metrics
            for task, success in results:
                self.session.total_attempts += 1
                
                if success:
                    self.session.successful_proofs += 1
                    self.completed_tasks[task.task_id] = task
                    logger.info(f"✅ Proved: {task.lemma_name}")
                else:
                    self.session.failed_proofs += 1
                    if task.attempts < task.max_attempts:
                        # Re-queue with lower priority
                        task.priority = max(1, task.priority - 1)
                        self.task_queue.append(task)
                    else:
                        logger.warning(f"❌ Failed after {task.attempts} attempts: {task.lemma_name}")
                        self.completed_tasks[task.task_id] = task
                
                self.monitor.record_proof_attempt(task, success)
            
            # Periodic checkpoint
            if datetime.now() - self.session.last_checkpoint > timedelta(minutes=30):
                self.save_checkpoint()
                self.session.last_checkpoint = datetime.now()
            
            # Brief pause to avoid overwhelming the system
            await asyncio.sleep(1)
        
        # Final report
        self._generate_final_report()
    
    async def _initialize_tasks(self, targets: List[str]):
        """Initialize proof tasks from target files/axioms"""
        from theorem_decomposition_framework import DecompositionOrchestrator
        
        orchestrator = DecompositionOrchestrator(self.api_key)
        
        for target in targets:
            if target.endswith('.lean'):
                # Process file
                results = await orchestrator.process_file(target)
                # Convert to tasks
                for theorem_name, graph in orchestrator.graphs.items():
                    for lemma_id, lemma in graph.nodes.items():
                        task = ProofTask(
                            task_id=f"{theorem_name}_{lemma_id}",
                            axiom_name=theorem_name,
                            lemma_name=lemma.name,
                            statement=lemma.statement,
                            dependencies=[d for d in lemma.dependencies],
                            priority=5 - lemma.difficulty.value  # Higher difficulty = lower priority
                        )
                        self.task_queue.append(task)
            else:
                # Process individual axiom
                # This would decompose the axiom as in run_systematic_decomposition.py
                pass
        
        # Sort by priority and dependencies
        self._sort_task_queue()
    
    def _sort_task_queue(self):
        """Sort task queue by priority and dependencies"""
        # Build dependency graph
        dep_graph = {}
        for task in self.task_queue:
            dep_graph[task.task_id] = task.dependencies
        
        # Topological sort with priority
        sorted_tasks = []
        visited = set()
        
        def visit(task_id):
            if task_id in visited:
                return
            visited.add(task_id)
            
            task = next((t for t in self.task_queue if t.task_id == task_id), None)
            if task:
                for dep in task.dependencies:
                    visit(dep)
                sorted_tasks.append(task)
        
        # Visit all tasks
        for task in sorted(self.task_queue, key=lambda t: t.priority, reverse=True):
            visit(task.task_id)
        
        self.task_queue = sorted_tasks
    
    def _get_next_batch(self, batch_size: int) -> List[ProofTask]:
        """Get next batch of tasks to process"""
        batch = []
        
        for task in self.task_queue[:]:
            # Check if dependencies are satisfied
            deps_satisfied = all(
                dep in self.completed_tasks and self.completed_tasks[dep].is_proven
                for dep in task.dependencies
            )
            
            if deps_satisfied:
                batch.append(task)
                self.task_queue.remove(task)
                
                if len(batch) >= batch_size:
                    break
        
        return batch
    
    async def _process_batch_parallel(self, batch: List[ProofTask]) -> List[Tuple[ProofTask, bool]]:
        """Process a batch of proof tasks in parallel"""
        from scaffolding_solver import ScaffoldingSolver
        
        solver = ScaffoldingSolver()
        results = []
        
        # Create async tasks for each proof
        async_tasks = []
        for task in batch:
            # Get best strategies for this task
            strategies = self.strategy.get_best_strategies(task)
            async_tasks.append(self._attempt_proof_with_strategies(task, strategies, solver))
        
        # Wait for all to complete
        completed = await asyncio.gather(*async_tasks)
        
        return completed
    
    async def _attempt_proof_with_strategies(self, task: ProofTask, strategies: List[str], 
                                           solver) -> Tuple[ProofTask, bool]:
        """Attempt to prove a task using multiple strategies"""
        task.attempts += 1
        
        for strategy in strategies:
            try:
                # Convert strategy to prompt modifier
                prompt_modifier = self._strategy_to_prompt(strategy)
                
                # Attempt proof
                result = await solver.attempt_proof_with_ai({
                    "file_path": task.axiom_name,
                    "line_number": 0,
                    "function_name": task.lemma_name,
                    "context": task.statement + f"\n{prompt_modifier}",
                    "difficulty": "MEDIUM"
                })
                
                if result.success:
                    task.proof_code = result.proof_code
                    task.is_proven = True
                    self.strategy.record_attempt(task, strategy, True)
                    return task, True
                else:
                    self.strategy.record_attempt(task, strategy, False)
                    
            except Exception as e:
                logger.error(f"Error attempting proof with {strategy}: {e}")
                task.last_error = str(e)
        
        return task, False
    
    def _strategy_to_prompt(self, strategy: str) -> str:
        """Convert strategy name to prompt modifier"""
        prompts = {
            "simp_first": "Start with simp to simplify the goal, then proceed.",
            "case_split": "Use case analysis on the relevant hypotheses.",
            "induction": "Use induction on the appropriate variable.",
            "contradiction": "Try proof by contradiction (by_contra).",
            "calculation": "Use calc mode for chained equalities/inequalities.",
            "mathlib_search": "Search for relevant Mathlib lemmas and apply them."
        }
        return prompts.get(strategy, "")
    
    def _generate_final_report(self):
        """Generate comprehensive final report"""
        report = [
            f"# Autonomous Proof Session Report",
            f"Session ID: {self.session.session_id}",
            f"Duration: {datetime.now() - self.session.start_time}",
            "",
            "## Summary Statistics",
            f"- Total proof attempts: {self.session.total_attempts}",
            f"- Successful proofs: {self.session.successful_proofs}",
            f"- Failed proofs: {self.session.failed_proofs}",
            f"- Success rate: {self.session.successful_proofs / max(1, self.session.total_attempts) * 100:.1f}%",
            "",
            "## Performance Metrics",
        ]
        
        perf = self.monitor.get_performance_summary()
        for key, value in perf.items():
            report.append(f"- {key}: {value}")
        
        report.extend([
            "",
            "## Strategy Effectiveness",
        ])
        
        for strategy, stats in self.strategy.strategy_success.items():
            if stats["attempts"] > 0:
                rate = stats["successes"] / stats["attempts"] * 100
                report.append(f"- {strategy}: {stats['successes']}/{stats['attempts']} ({rate:.1f}%)")
        
        report.extend([
            "",
            "## Completed Proofs",
        ])
        
        for task_id, task in self.completed_tasks.items():
            if task.is_proven:
                report.append(f"- ✅ {task.lemma_name} (attempts: {task.attempts})")
        
        report_path = self.checkpoint_dir / f"report_{self.session.session_id}.md"
        with open(report_path, 'w') as f:
            f.write('\n'.join(report))
        
        logger.info(f"Final report saved to {report_path}")

async def main():
    """Example usage of the autonomous runner"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Run autonomous proof session")
    parser.add_argument("targets", nargs="+", help="Target files or axioms to prove")
    parser.add_argument("--api-key", help="Anthropic API key")
    parser.add_argument("--session-id", help="Session ID")
    parser.add_argument("--resume", help="Resume from checkpoint file")
    parser.add_argument("--max-hours", type=int, default=24, help="Maximum runtime in hours")
    
    args = parser.parse_args()
    
    # Get API key
    api_key = args.api_key or os.getenv("ANTHROPIC_API_KEY")
    if not api_key:
        print("Error: No API key provided")
        return
    
    # Create runner
    runner = AutonomousProofRunner(api_key)
    runner.monitor.max_time = timedelta(hours=args.max_hours)
    
    # Run session
    await runner.run_proof_session(
        targets=args.targets,
        session_id=args.session_id,
        resume_from_checkpoint=args.resume
    )

if __name__ == "__main__":
    asyncio.run(main()) 