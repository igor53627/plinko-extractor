#!/usr/bin/env python3
"""
Results Analysis for SR PRP Optimization Experiments

Analyzes benchmark results and generates reports.
"""

import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


RESULTS_DIR = Path(__file__).parent / "results"


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


def load_results(results_dir: Path = RESULTS_DIR) -> list[BenchmarkResult]:
    """Load all results from the results directory."""
    results = []
    for path in sorted(results_dir.glob("*.json")):
        try:
            with open(path) as f:
                data = json.load(f)
            results.append(BenchmarkResult(**data))
        except (json.JSONDecodeError, TypeError) as e:
            print(f"Warning: Failed to load {path}: {e}", file=sys.stderr)
    return results


def fitness(result: BenchmarkResult) -> float:
    """Compute fitness score."""
    if not result.correctness or result.time_seconds < 0:
        return 0.0
    speed_score = 1.0 / result.time_seconds if result.time_seconds > 0 else 0
    speed_score = speed_score * 1000
    memory_penalty = min(result.memory_mb / 1000.0, 1.0) * 0.1
    security_factor = result.security_bits / 128.0
    return speed_score * (1.0 - memory_penalty) * security_factor


def print_summary(results: list[BenchmarkResult]):
    """Print summary statistics."""
    if not results:
        print("No results found.")
        return
    
    valid = [r for r in results if r.correctness and r.time_seconds > 0]
    invalid = [r for r in results if not r.correctness or r.time_seconds < 0]
    
    print("=" * 70)
    print("SR PRP Optimization Results Summary")
    print("=" * 70)
    print(f"Total experiments: {len(results)}")
    print(f"Valid results: {len(valid)}")
    print(f"Failed/Invalid: {len(invalid)}")
    print()
    
    if not valid:
        print("No valid results to analyze.")
        return
    
    # Best results
    by_fitness = sorted(valid, key=fitness, reverse=True)
    by_time = sorted(valid, key=lambda r: r.time_seconds)
    by_security = sorted(valid, key=lambda r: -r.security_bits)
    
    print("Top 5 by Fitness:")
    print("-" * 70)
    print(f"{'Rank':<5} {'Config':<30} {'Time (s)':<12} {'Security':<10} {'Fitness':<10}")
    print("-" * 70)
    for i, r in enumerate(by_fitness[:5]):
        print(f"{i+1:<5} {r.config_name:<30} {r.time_seconds:<12.1f} {r.security_bits:<10} {fitness(r):<10.4f}")
    print()
    
    print("Top 5 by Speed:")
    print("-" * 70)
    print(f"{'Rank':<5} {'Config':<30} {'Time (s)':<12} {'Security':<10} {'Throughput':<10}")
    print("-" * 70)
    for i, r in enumerate(by_time[:5]):
        print(f"{i+1:<5} {r.config_name:<30} {r.time_seconds:<12.1f} {r.security_bits:<10} {r.throughput_entries_per_sec:<10.1f}")
    print()
    
    # Security level breakdown
    print("By Security Level:")
    print("-" * 70)
    security_groups = {}
    for r in valid:
        sec = r.security_bits
        if sec not in security_groups:
            security_groups[sec] = []
        security_groups[sec].append(r)
    
    for sec in sorted(security_groups.keys(), reverse=True):
        group = security_groups[sec]
        best = min(group, key=lambda r: r.time_seconds)
        avg_time = sum(r.time_seconds for r in group) / len(group)
        print(f"  {sec}-bit: {len(group)} experiments, best={best.time_seconds:.1f}s, avg={avg_time:.1f}s")
    print()
    
    # Failed experiments
    if invalid:
        print("Failed Experiments:")
        print("-" * 70)
        for r in invalid:
            reason = r.error or ("incorrect" if not r.correctness else "timeout/error")
            print(f"  {r.config_name}: {reason}")
        print()


def print_pareto_frontier(results: list[BenchmarkResult]):
    """Print Pareto-optimal configurations (speed vs security tradeoff)."""
    valid = [r for r in results if r.correctness and r.time_seconds > 0]
    if not valid:
        return
    
    # Find Pareto frontier
    pareto = []
    for r in valid:
        dominated = False
        for other in valid:
            if other is r:
                continue
            # other dominates r if: faster AND higher security
            if other.time_seconds <= r.time_seconds and other.security_bits >= r.security_bits:
                if other.time_seconds < r.time_seconds or other.security_bits > r.security_bits:
                    dominated = True
                    break
        if not dominated:
            pareto.append(r)
    
    pareto.sort(key=lambda r: -r.security_bits)
    
    print("Pareto Frontier (Speed vs Security):")
    print("-" * 70)
    print(f"{'Config':<35} {'Time (s)':<12} {'Security':<10} {'Memory (MB)':<12}")
    print("-" * 70)
    for r in pareto:
        print(f"{r.config_name:<35} {r.time_seconds:<12.1f} {r.security_bits:<10} {r.memory_mb:<12.1f}")
    print()


def generate_markdown_report(results: list[BenchmarkResult], output_path: Path):
    """Generate a markdown report."""
    valid = [r for r in results if r.correctness and r.time_seconds > 0]
    by_fitness = sorted(valid, key=fitness, reverse=True)
    
    lines = [
        "# SR PRP Optimization Results",
        "",
        f"Generated from {len(results)} experiments ({len(valid)} valid).",
        "",
        "## Top Performers",
        "",
        "| Rank | Config | Time (s) | Security | Fitness |",
        "|------|--------|----------|----------|---------|",
    ]
    
    for i, r in enumerate(by_fitness[:10]):
        lines.append(f"| {i+1} | {r.config_name} | {r.time_seconds:.1f} | {r.security_bits} | {fitness(r):.4f} |")
    
    lines.extend([
        "",
        "## Recommendations",
        "",
    ])
    
    if by_fitness:
        best = by_fitness[0]
        lines.append(f"**Best overall**: `{best.config_name}` with {best.time_seconds:.1f}s at {best.security_bits}-bit security.")
        
        # Best at 128-bit
        best_128 = [r for r in valid if r.security_bits == 128]
        if best_128:
            b = min(best_128, key=lambda r: r.time_seconds)
            lines.append(f"\n**Best at 128-bit security**: `{b.config_name}` with {b.time_seconds:.1f}s.")
        
        # Fastest overall
        fastest = min(valid, key=lambda r: r.time_seconds)
        lines.append(f"\n**Fastest**: `{fastest.config_name}` with {fastest.time_seconds:.1f}s ({fastest.security_bits}-bit).")
    
    output_path.write_text("\n".join(lines))
    print(f"Report written to: {output_path}")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Analyze SR PRP optimization results")
    parser.add_argument("--results-dir", type=Path, default=RESULTS_DIR)
    parser.add_argument("--report", type=Path, help="Generate markdown report")
    parser.add_argument("--pareto", action="store_true", help="Show Pareto frontier")
    
    args = parser.parse_args()
    
    results = load_results(args.results_dir)
    
    print_summary(results)
    
    if args.pareto:
        print_pareto_frontier(results)
    
    if args.report:
        generate_markdown_report(results, args.report)


if __name__ == "__main__":
    main()
