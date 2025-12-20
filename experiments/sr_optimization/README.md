# SR PRP Optimization Experiments

LLM-guided evolutionary search for optimizing Swap-or-Not Sometimes-Recurse PRP performance.

## Quick Start

```bash
# Run baseline experiments
python harness.py --phase baseline

# Run ablation study
python harness.py --phase ablation

# Run LLM-guided evolutionary search (8 iterations)
python harness.py --phase evolve --iterations 8

# Verify best candidate
python harness.py --phase verify --config combined_fast

# Analyze results
python analyze.py
python analyze.py --pareto --report results/report.md
```

## Directory Structure

```
sr_optimization/
  configs/           # JSON candidate configurations
  results/           # Benchmark outputs (JSON)
  harness.py         # Main orchestration script
  llm_proposer.py    # LLM integration for candidate generation
  analyze.py         # Results analysis and reporting
  README.md          # This file
```

## Configuration Format

```json
{
  "name": "config_name",
  "transforms": ["T1_PRECOMPUTE_KEYS", "T2_BATCH_AES"],
  "params": {
    "security_bits": 128,
    "batch_size": 8
  },
  "description": "Description of this configuration"
}
```

## Available Transforms

| ID | Transform | Description |
|----|-----------|-------------|
| T1 | PRECOMPUTE_KEYS | Cache all round keys at construction |
| T2 | BATCH_AES | Parallel AES-NI block encryption |
| T3 | LAZY_SR | Skip deep levels on early exit |
| T4 | SIMD_PRF | Vectorize prf_bit with SIMD |
| T5 | ROUND_UNROLL | Unroll inner loop (factor: 2/4/8) |
| T6 | CACHE_CANONICAL | Memoize canonical computations |
| T7 | REDUCED_SECURITY | Allow security_bits < 128 |

## Parameters

| Parameter | Values | Default | Description |
|-----------|--------|---------|-------------|
| security_bits | 32, 64, 80, 96, 128 | 128 | Lambda for round count formula |
| batch_size | 1, 2, 4, 8, 16 | 1 | AES blocks processed in parallel |
| unroll_factor | 2, 4, 8 | 4 | Loop unrolling factor |

## LLM Integration

Set `ANTHROPIC_API_KEY` environment variable to enable LLM-guided proposals:

```bash
export ANTHROPIC_API_KEY="your-key-here"
python harness.py --phase evolve
```

Without the API key, the harness falls back to heuristic mutation/crossover strategies.

## Results

Results are saved as JSON in `results/`:

```json
{
  "config_name": "batch_aes_8",
  "time_seconds": 123.45,
  "throughput_entries_per_sec": 100.5,
  "memory_mb": 50.0,
  "correctness": true,
  "security_bits": 128,
  "timestamp": "20241220_143022"
}
```

## Issue Reference

This addresses [Issue #63](https://github.com/igor53627/plinko-extractor/issues/63): Optimize SR PRP performance (~50x regression).
