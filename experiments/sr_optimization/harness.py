#!/usr/bin/env python3
"""
SR PRP Optimization Harness

Orchestrates LLM-guided evolutionary search for optimizing Swap-or-Not
Sometimes-Recurse PRP performance.

Usage:
    python harness.py --phase baseline    # Run Phase 1 baselines
    python harness.py --phase ablation    # Run Phase 2 ablation
    python harness.py --phase evolve      # Run Phase 3 LLM-guided search
    python harness.py --phase verify      # Run Phase 4 verification
"""

import argparse
import json
import os
import subprocess
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import Optional

WORKSPACE_ROOT = Path(__file__).parent.parent.parent
STATE_SYNCER_DIR = WORKSPACE_ROOT / "state-syncer"
CONFIGS_DIR = Path(__file__).parent / "configs"
RESULTS_DIR = Path(__file__).parent / "results"


@dataclass
class CandidateConfig:
    name: str
    transforms: list[str]
    params: dict
    description: str = ""


@dataclass
class BenchmarkResult:
    config_name: str
    time_seconds: float
    throughput_entries_per_sec: float
    memory_mb: float
    correctness: bool
    security_bits: int
    timestamp: str
    error: Optional[str] = None


def load_config(config_path: Path) -> CandidateConfig:
    with open(config_path) as f:
        data = json.load(f)
    return CandidateConfig(**data)


def save_result(result: BenchmarkResult, results_dir: Path = RESULTS_DIR):
    results_dir.mkdir(parents=True, exist_ok=True)
    result_path = results_dir / f"{result.config_name}_{result.timestamp}.json"
    with open(result_path, "w") as f:
        json.dump(asdict(result), f, indent=2)
    return result_path


def apply_transforms(config: CandidateConfig) -> bool:
    """
    Apply code transformations based on config.
    Returns True if successful, False otherwise.
    
    Transform implementations:
    - T1_PRECOMPUTE_KEYS: Already in base code
    - T2_BATCH_AES: Enable batch AES feature
    - T3_LAZY_SR: Enable lazy SR evaluation
    - T4_SIMD_PRF: Enable SIMD vectorization
    - T5_ROUND_UNROLL: Set unroll factor
    - T6_CACHE_CANONICAL: Enable canonical caching
    - T7_REDUCED_SECURITY: Set security_bits param
    """
    features = []
    env_vars = {}
    
    for transform in config.transforms:
        if transform == "T1_PRECOMPUTE_KEYS":
            pass  # Already in base implementation
        elif transform == "T2_BATCH_AES":
            features.append("batch_aes")
        elif transform == "T3_LAZY_SR":
            features.append("lazy_sr")
        elif transform == "T4_SIMD_PRF":
            features.append("simd_prf")
        elif transform == "T5_ROUND_UNROLL":
            unroll_factor = config.params.get("unroll_factor", 4)
            env_vars["UNROLL_FACTOR"] = str(unroll_factor)
            features.append("round_unroll")
        elif transform == "T6_CACHE_CANONICAL":
            features.append("cache_canonical")
        elif transform == "T7_REDUCED_SECURITY":
            pass  # Handled via params
    
    # Set security bits
    security_bits = config.params.get("security_bits", 128)
    env_vars["SR_SECURITY_BITS"] = str(security_bits)
    
    # Set batch size
    batch_size = config.params.get("batch_size", 1)
    env_vars["SR_BATCH_SIZE"] = str(batch_size)
    
    # Write environment config
    env_path = STATE_SYNCER_DIR / ".env.experiment"
    with open(env_path, "w") as f:
        for k, v in env_vars.items():
            f.write(f"{k}={v}\n")
    
    # Write features config
    features_path = STATE_SYNCER_DIR / ".features.experiment"
    with open(features_path, "w") as f:
        f.write(",".join(features))
    
    return True


def build_candidate(config: CandidateConfig) -> tuple[bool, str]:
    """Build the candidate with applied transforms."""
    features_path = STATE_SYNCER_DIR / ".features.experiment"
    features = ""
    if features_path.exists():
        features = features_path.read_text().strip()
    
    cmd = ["cargo", "build", "--release", "--bin", "bench_hints"]
    if features:
        cmd.extend(["--features", features])
    
    try:
        result = subprocess.run(
            cmd,
            cwd=STATE_SYNCER_DIR,
            capture_output=True,
            text=True,
            timeout=300
        )
        if result.returncode != 0:
            return False, result.stderr
        return True, ""
    except subprocess.TimeoutExpired:
        return False, "Build timeout"
    except Exception as e:
        return False, str(e)


def run_benchmark(
    config: CandidateConfig,
    db_path: str = "/mnt/plinko/sample.bin",
    block_size: int = 4096
) -> tuple[float, float, float]:
    """
    Run benchmark and return (time_seconds, throughput, memory_mb).
    """
    env_path = STATE_SYNCER_DIR / ".env.experiment"
    env = os.environ.copy()
    if env_path.exists():
        for line in env_path.read_text().strip().split("\n"):
            if "=" in line:
                k, v = line.split("=", 1)
                env[k] = v
    
    cmd = [
        str(STATE_SYNCER_DIR / "target/release/bench_hints"),
        "--db-path", db_path,
        "--block-size", str(block_size)
    ]
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=3600,  # 1 hour max
            env=env
        )
        elapsed = time.time() - start_time
        
        if result.returncode != 0:
            return -1, 0, 0
        
        # Parse output for metrics
        throughput = 0.0
        memory = 0.0
        for line in result.stdout.split("\n"):
            if "Throughput:" in line:
                # "Throughput: 123.45 MB/s"
                parts = line.split()
                if len(parts) >= 2:
                    try:
                        throughput = float(parts[1])
                    except ValueError:
                        pass
            if "Client Hint Storage:" in line:
                # "Client Hint Storage: 123.45 MB"
                parts = line.split()
                if len(parts) >= 4:
                    try:
                        memory = float(parts[3])
                    except ValueError:
                        pass
        
        return elapsed, throughput, memory
        
    except subprocess.TimeoutExpired:
        return -1, 0, 0
    except Exception:
        return -1, 0, 0


def run_correctness_tests(config: CandidateConfig) -> bool:
    """Run PRP correctness tests."""
    security_bits = config.params.get("security_bits", 128)
    
    # For lower security, tests run faster
    test_name = "test_sr_with_custom_security" if security_bits < 128 else "test_swap_or_not_sr_inverse"
    
    cmd = [
        "cargo", "test", "--release",
        "--", "--ignored", test_name
    ]
    
    try:
        result = subprocess.run(
            cmd,
            cwd=STATE_SYNCER_DIR,
            capture_output=True,
            text=True,
            timeout=600
        )
        return result.returncode == 0
    except Exception:
        return False


def evaluate_candidate(config: CandidateConfig, db_path: str = "/mnt/plinko/sample.bin") -> BenchmarkResult:
    """Full evaluation pipeline for a candidate."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    # Apply transforms
    if not apply_transforms(config):
        return BenchmarkResult(
            config_name=config.name,
            time_seconds=-1,
            throughput_entries_per_sec=0,
            memory_mb=0,
            correctness=False,
            security_bits=config.params.get("security_bits", 128),
            timestamp=timestamp,
            error="Failed to apply transforms"
        )
    
    # Build
    success, error = build_candidate(config)
    if not success:
        return BenchmarkResult(
            config_name=config.name,
            time_seconds=-1,
            throughput_entries_per_sec=0,
            memory_mb=0,
            correctness=False,
            security_bits=config.params.get("security_bits", 128),
            timestamp=timestamp,
            error=f"Build failed: {error}"
        )
    
    # Benchmark
    time_sec, throughput, memory = run_benchmark(config, db_path)
    if time_sec < 0:
        return BenchmarkResult(
            config_name=config.name,
            time_seconds=-1,
            throughput_entries_per_sec=0,
            memory_mb=0,
            correctness=False,
            security_bits=config.params.get("security_bits", 128),
            timestamp=timestamp,
            error="Benchmark failed or timed out"
        )
    
    # Correctness
    correct = run_correctness_tests(config)
    
    return BenchmarkResult(
        config_name=config.name,
        time_seconds=time_sec,
        throughput_entries_per_sec=throughput,
        memory_mb=memory,
        correctness=correct,
        security_bits=config.params.get("security_bits", 128),
        timestamp=timestamp
    )


def fitness(result: BenchmarkResult) -> float:
    """Compute fitness score for a benchmark result."""
    if not result.correctness or result.time_seconds < 0:
        return 0.0
    
    # Primary: speed (inverse of time)
    speed_score = 1.0 / result.time_seconds if result.time_seconds > 0 else 0
    
    # Normalize to reasonable range (assuming baseline ~3000s, target ~300s)
    speed_score = speed_score * 1000
    
    # Memory penalty (soft)
    memory_penalty = min(result.memory_mb / 1000.0, 1.0) * 0.1
    
    # Security bonus
    security_factor = result.security_bits / 128.0
    
    return speed_score * (1.0 - memory_penalty) * security_factor


def run_phase_baseline():
    """Phase 1: Baseline characterization."""
    print("=" * 60)
    print("Phase 1: Baseline Characterization")
    print("=" * 60)
    
    baselines = [
        CandidateConfig(
            name="baseline_128",
            transforms=["T1_PRECOMPUTE_KEYS"],
            params={"security_bits": 128, "batch_size": 1},
            description="Full security baseline with precomputed keys"
        ),
        CandidateConfig(
            name="baseline_64",
            transforms=["T1_PRECOMPUTE_KEYS"],
            params={"security_bits": 64, "batch_size": 1},
            description="Reduced security (64-bit)"
        ),
        CandidateConfig(
            name="baseline_32",
            transforms=["T1_PRECOMPUTE_KEYS"],
            params={"security_bits": 32, "batch_size": 1},
            description="Low security (32-bit) for speed reference"
        ),
    ]
    
    results = []
    for config in baselines:
        print(f"\nEvaluating: {config.name}")
        print(f"  Transforms: {config.transforms}")
        print(f"  Params: {config.params}")
        
        result = evaluate_candidate(config)
        results.append(result)
        
        save_result(result)
        
        print(f"  Time: {result.time_seconds:.2f}s")
        print(f"  Throughput: {result.throughput_entries_per_sec:.2f} MB/s")
        print(f"  Correct: {result.correctness}")
        if result.error:
            print(f"  Error: {result.error}")
    
    return results


def run_phase_ablation():
    """Phase 2: Single-transformation ablation study."""
    print("=" * 60)
    print("Phase 2: Ablation Study")
    print("=" * 60)
    
    # Base: T1 with 64-bit security for faster iteration
    base_transforms = ["T1_PRECOMPUTE_KEYS"]
    base_params = {"security_bits": 64, "batch_size": 1}
    
    ablation_transforms = [
        ("T2_BATCH_AES", {"batch_size": 8}),
        ("T3_LAZY_SR", {}),
        ("T5_ROUND_UNROLL", {"unroll_factor": 4}),
    ]
    
    results = []
    for transform, extra_params in ablation_transforms:
        config = CandidateConfig(
            name=f"ablation_{transform.lower()}",
            transforms=base_transforms + [transform],
            params={**base_params, **extra_params},
            description=f"Ablation: {transform}"
        )
        
        print(f"\nEvaluating: {config.name}")
        result = evaluate_candidate(config)
        results.append(result)
        save_result(result)
        
        print(f"  Time: {result.time_seconds:.2f}s")
        print(f"  Fitness: {fitness(result):.4f}")
    
    return results


def run_phase_evolve(iterations: int = 8):
    """Phase 3: LLM-guided evolutionary search."""
    print("=" * 60)
    print("Phase 3: LLM-Guided Evolutionary Search")
    print("=" * 60)
    
    from llm_proposer import LLMProposer
    
    proposer = LLMProposer()
    
    # Initialize population
    population = [
        CandidateConfig(
            name="evo_base",
            transforms=["T1_PRECOMPUTE_KEYS"],
            params={"security_bits": 128, "batch_size": 1},
            description="Baseline"
        ),
        CandidateConfig(
            name="evo_batch8",
            transforms=["T1_PRECOMPUTE_KEYS", "T2_BATCH_AES"],
            params={"security_bits": 128, "batch_size": 8},
            description="Batch AES"
        ),
        CandidateConfig(
            name="evo_lazy",
            transforms=["T1_PRECOMPUTE_KEYS", "T3_LAZY_SR"],
            params={"security_bits": 128, "batch_size": 1},
            description="Lazy SR"
        ),
        CandidateConfig(
            name="evo_combined",
            transforms=["T1_PRECOMPUTE_KEYS", "T2_BATCH_AES", "T3_LAZY_SR"],
            params={"security_bits": 128, "batch_size": 8},
            description="Combined optimizations"
        ),
        CandidateConfig(
            name="evo_fast",
            transforms=["T1_PRECOMPUTE_KEYS", "T2_BATCH_AES", "T3_LAZY_SR"],
            params={"security_bits": 64, "batch_size": 8},
            description="Speed-focused with reduced security"
        ),
    ]
    
    all_results = []
    
    for iteration in range(iterations):
        print(f"\n{'='*40}")
        print(f"Iteration {iteration + 1}/{iterations}")
        print(f"{'='*40}")
        
        # Evaluate population
        results = []
        for config in population:
            print(f"  Evaluating: {config.name}")
            result = evaluate_candidate(config)
            results.append((config, result))
            save_result(result)
        
        # Rank by fitness
        ranked = sorted(results, key=lambda x: fitness(x[1]), reverse=True)
        all_results.extend([r for _, r in ranked])
        
        print("\n  Rankings:")
        for i, (config, result) in enumerate(ranked[:5]):
            print(f"    {i+1}. {config.name}: {fitness(result):.4f} ({result.time_seconds:.1f}s)")
        
        if iteration < iterations - 1:
            # Get LLM proposals for next iteration
            new_configs = proposer.propose(ranked, iteration)
            
            # Selection: keep top 5 + add new proposals
            population = [c for c, _ in ranked[:5]] + new_configs
    
    # Return best result
    best = max(all_results, key=fitness)
    print(f"\nBest result: {best.config_name}")
    print(f"  Time: {best.time_seconds:.2f}s")
    print(f"  Fitness: {fitness(best):.4f}")
    
    return all_results


def run_phase_verify(config_name: str):
    """Phase 4: Verify best candidate."""
    print("=" * 60)
    print("Phase 4: Verification")
    print("=" * 60)
    
    # Load config
    config_path = CONFIGS_DIR / f"{config_name}.json"
    if not config_path.exists():
        print(f"Config not found: {config_path}")
        return False
    
    config = load_config(config_path)
    apply_transforms(config)
    
    # Full correctness suite
    tests = [
        "test_swap_or_not_sr_inverse",
        "test_swap_or_not_sr_is_permutation",
        "test_swap_or_not_sr_tee_matches_standard",
    ]
    
    all_passed = True
    for test in tests:
        print(f"  Running: {test}")
        cmd = ["cargo", "test", "--release", "--", "--ignored", test]
        result = subprocess.run(cmd, cwd=STATE_SYNCER_DIR, capture_output=True, text=True)
        passed = result.returncode == 0
        print(f"    {'[PASS]' if passed else '[FAIL]'}")
        all_passed = all_passed and passed
    
    return all_passed


def main():
    parser = argparse.ArgumentParser(description="SR PRP Optimization Harness")
    parser.add_argument(
        "--phase",
        choices=["baseline", "ablation", "evolve", "verify"],
        required=True,
        help="Experiment phase to run"
    )
    parser.add_argument(
        "--iterations",
        type=int,
        default=8,
        help="Number of evolution iterations (for evolve phase)"
    )
    parser.add_argument(
        "--config",
        type=str,
        help="Config name to verify (for verify phase)"
    )
    parser.add_argument(
        "--db-path",
        type=str,
        default="/mnt/plinko/sample.bin",
        help="Path to benchmark database"
    )
    
    args = parser.parse_args()
    
    if args.phase == "baseline":
        run_phase_baseline()
    elif args.phase == "ablation":
        run_phase_ablation()
    elif args.phase == "evolve":
        run_phase_evolve(args.iterations)
    elif args.phase == "verify":
        if not args.config:
            print("Error: --config required for verify phase")
            return 1
        success = run_phase_verify(args.config)
        return 0 if success else 1
    
    return 0


if __name__ == "__main__":
    exit(main())
