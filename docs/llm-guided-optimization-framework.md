# LLM-Guided Evolutionary Search for SR PRP Optimization

Framework for optimizing Swap-or-Not Sometimes-Recurse PRP performance using LLM-guided evolutionary search, inspired by the SDE framework (arXiv:2512.15567).

## Problem Statement

**Objective**: Reduce hint generation time from ~50 min to <5 min (10x improvement) while maintaining cryptographic security guarantees.

**Root Cause**: Morris-Rogaway Eq. 2 round formula `t_N = ceil(7.23 lg N + 4.82 lambda + 4.82 lg p)` with lambda=128 produces ~770 rounds/level vs old heuristic ~134 rounds (~5.7x more). Combined with ~21 SR recursion levels = massive overhead.

**Bottleneck**: Each round performs 2 AES encryptions:
1. `derive_round_key()` - deterministic per (round, domain)
2. `prf_bit()` - depends on input value

## Search Space Definition

### 1. Algorithmic Parameters

**Security constraint: lambda=128 is FIXED. No security tradeoffs allowed.**

| Parameter | Range | Current | Description |
|-----------|-------|---------|-------------|
| `security_bits` | **128** | 128 | Lambda parameter (FIXED) |
| `batch_size` | 1-16 | 1 | AES blocks processed in parallel |
| `prefetch_depth` | 0-4 | 0 | Cache prefetch lookahead |
| `parallel_elements` | 1-1024 | 1 | Elements batched through same round |

### 2. Code Transformations

| Transform ID | Description | Security Impact |
|--------------|-------------|-----------------|
| `T1_PRECOMPUTE_KEYS` | Cache all round keys at construction | None (done) |
| `T2_BATCH_AES` | Use `encrypt_blocks()` for parallel AES-NI | None |
| `T3_LAZY_SR` | Skip deep levels when value exits early | None |
| `T4_SIMD_PRF` | Vectorize prf_bit with AVX2/NEON | None |
| `T5_ROUND_UNROLL` | Unroll inner round loop by factor k | None |
| `T6_BATCH_ELEMENTS` | Process multiple elements through same round | None |
| `T7_RAYON_PARALLEL` | Parallelize across CPU cores with rayon | None |

### 3. Architectural Variants

| Variant | Description |
|---------|-------------|
| `STREAMING` | Process entries one at a time (current) |
| `BATCH_LEVEL` | Batch entries at same SR level together |
| `BATCH_ROUND` | Batch entries through same round together |
| `HYBRID` | Streaming with opportunistic batching |

## Oracle Function (Fitness Evaluation)

```rust
struct BenchmarkResult {
    time_seconds: f64,
    throughput_entries_per_sec: f64,
    memory_mb: f64,
    correctness: bool,  // Must pass inverse roundtrip test
    security_bits: u32,
}

fn evaluate_candidate(config: &CandidateConfig) -> BenchmarkResult {
    // 1. Apply code transformations
    // 2. Build with --release
    // 3. Run benchmark on sample dataset (3.6GB, 120M entries)
    // 4. Verify correctness via PRP inverse tests
    // 5. Return metrics
}

fn fitness(result: &BenchmarkResult) -> f64 {
    if !result.correctness {
        return 0.0;  // Invalid candidate
    }
    
    // Multi-objective: speed (primary), memory (secondary), security (constraint)
    let speed_score = result.throughput_entries_per_sec / 1_000_000.0;  // Normalize
    let memory_penalty = (result.memory_mb / 1000.0).min(1.0);
    let security_bonus = (result.security_bits as f64) / 128.0;
    
    speed_score * (1.0 - 0.1 * memory_penalty) * security_bonus
}
```

## Experiment Protocol

### Phase 1: Baseline Characterization

**Goal**: Establish performance baselines for different security levels.

| Experiment | Config | Metric |
|------------|--------|--------|
| E1.1 | lambda=128, no optimizations | Baseline time |
| E1.2 | lambda=64 | Time reduction |
| E1.3 | lambda=32 | Time reduction |
| E1.4 | Precompute keys only | Phase 1 optimization |

### Phase 2: Single-Transformation Ablation

**Goal**: Measure individual contribution of each transformation.

```
For each T in {T2_BATCH_AES, T3_LAZY_SR, T4_SIMD_PRF, T5_ROUND_UNROLL, T6_CACHE_CANONICAL}:
    1. Apply T to baseline (with T1 already applied)
    2. Measure time, memory, correctness
    3. Record delta vs baseline
```

### Phase 3: LLM-Guided Search

**Goal**: Find optimal combination of transformations and parameters.

#### Initialization
```python
population = [
    {"transforms": ["T1"], "params": {"lambda": 128, "batch": 1}},  # Baseline
    {"transforms": ["T1", "T2"], "params": {"lambda": 128, "batch": 8}},
    {"transforms": ["T1", "T3"], "params": {"lambda": 128, "batch": 1}},
    {"transforms": ["T1", "T2", "T3"], "params": {"lambda": 128, "batch": 8}},
    {"transforms": ["T1"], "params": {"lambda": 64, "batch": 1}},  # Reduced security
]
```

#### Evolution Loop (8 iterations)

```
For iteration in 1..8:
    1. Evaluate all candidates in population
    2. Rank by fitness
    3. Prompt LLM with:
       - Top 5 performers with their configs and scores
       - Bottom 3 performers (to learn what doesn't work)
       - Remaining budget
    4. LLM proposes 3-5 new candidates via:
       - Mutation: Modify params of top performer
       - Crossover: Combine transforms from two parents
       - De novo: Propose novel combination based on patterns
    5. Add proposals to population
    6. Selection: Keep top 10 candidates
```

#### LLM Prompt Template

```markdown
## SR PRP Optimization Search - Iteration {N}

### Top Performers
| Rank | Config | Time (s) | Throughput | Memory | Security |
|------|--------|----------|------------|--------|----------|
{top_5_table}

### Failed/Poor Candidates
{bottom_3_with_reasons}

### Search History Summary
- Best time achieved: {best_time}s
- Best config: {best_config}
- Transforms that consistently help: {helpful_transforms}
- Transforms that hurt or are neutral: {unhelpful_transforms}

### Task
Propose 3-5 new candidate configurations to try. For each:
1. Specify transforms to apply (from T1-T7)
2. Specify parameters (lambda, batch_size, etc.)
3. Explain your reasoning

Consider:
- Unexplored combinations
- Parameter tuning of successful configs
- Novel structural changes to the algorithm
```

### Phase 4: Verification

**Goal**: Validate best candidate maintains security properties.

1. **Correctness**: Full inverse roundtrip test on 1M random inputs
2. **Permutation**: Verify output is a bijection for small domains
3. **Statistical**: Chi-squared test for output distribution uniformity
4. **Security Proof**: Verify round counts still satisfy Morris-Rogaway bounds

## Implementation Harness

### Directory Structure

```
experiments/
  sr_optimization/
    configs/           # JSON candidate configs
    results/           # Benchmark outputs
    harness.py         # Orchestration script
    analyze.py         # Results analysis
    llm_proposer.py    # LLM integration for candidate generation
```

### Harness Pseudocode

```python
def run_experiment(config_path: str) -> BenchmarkResult:
    config = load_json(config_path)
    
    # Generate patched source
    patched_src = apply_transforms(
        base_src="state-syncer/src/iprf.rs",
        transforms=config["transforms"],
        params=config["params"]
    )
    
    # Build
    write_file("state-syncer/src/iprf_candidate.rs", patched_src)
    run("cargo build --release --features candidate")
    
    # Benchmark
    result = run("./target/release/bench_hints --db-path /mnt/plinko/sample.bin")
    
    # Correctness check
    correct = run("cargo test --release -- --ignored test_swap_or_not_sr")
    
    return parse_result(result, correct)

def evolution_loop(iterations=8):
    population = initialize_population()
    
    for i in range(iterations):
        # Evaluate
        results = [run_experiment(c) for c in population]
        
        # Rank
        ranked = sorted(zip(population, results), key=lambda x: fitness(x[1]), reverse=True)
        
        # LLM proposal
        prompt = format_prompt(ranked, i)
        new_candidates = call_llm(prompt)
        
        # Selection
        population = [c for c, _ in ranked[:10]] + new_candidates
    
    return ranked[0]  # Best candidate
```

## Success Criteria

| Metric | Target | Stretch |
|--------|--------|---------|
| Sample benchmark time | <5 min | <2 min |
| Full mainnet time | <30 min | <10 min |
| Security level | >=64 bits | 128 bits |
| Memory overhead | <2x baseline | <1.5x |
| Correctness | 100% | 100% |

## Risk Analysis

| Risk | Mitigation |
|------|------------|
| Reduced security with lower lambda | Document security tradeoffs; offer tiered options |
| Batching breaks constant-time TEE variant | Separate non-TEE and TEE implementations |
| LLM proposes invalid transforms | Validate all proposals before benchmarking |
| Overfitting to sample dataset | Validate on multiple dataset sizes |

## Next Steps

1. [ ] Implement benchmark harness with config-driven transforms
2. [ ] Run Phase 1 baseline experiments
3. [ ] Run Phase 2 ablation study
4. [ ] Integrate LLM proposer (can use Amp/Claude API)
5. [ ] Execute Phase 3 evolutionary search
6. [ ] Document and merge best solution
