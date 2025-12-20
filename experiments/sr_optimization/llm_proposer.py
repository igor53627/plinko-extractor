#!/usr/bin/env python3
"""
LLM Proposer for SR PRP Optimization

Generates new candidate configurations using LLM-guided mutation,
crossover, and de novo proposal strategies.
"""

import json
import os
import random
from dataclasses import dataclass
from typing import Optional

# Try to import anthropic, fall back to mock if not available
try:
    import anthropic
    HAS_ANTHROPIC = True
except ImportError:
    HAS_ANTHROPIC = False


@dataclass
class CandidateConfig:
    name: str
    transforms: list[str]
    params: dict
    description: str = ""


AVAILABLE_TRANSFORMS = [
    "T1_PRECOMPUTE_KEYS",
    "T2_BATCH_AES",
    "T3_LAZY_SR",
    "T4_SIMD_PRF",
    "T5_ROUND_UNROLL",
    "T6_CACHE_CANONICAL",
    "T7_REDUCED_SECURITY",
]

PARAM_RANGES = {
    "security_bits": [32, 64, 80, 96, 128],
    "batch_size": [1, 2, 4, 8, 16],
    "unroll_factor": [2, 4, 8],
    "early_exit_threshold": [0.3, 0.5, 0.7],
}


class LLMProposer:
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.environ.get("ANTHROPIC_API_KEY")
        self.client = None
        if HAS_ANTHROPIC and self.api_key:
            self.client = anthropic.Anthropic(api_key=self.api_key)
        self.proposal_count = 0
    
    def format_results_table(self, ranked: list[tuple]) -> str:
        """Format ranked results as markdown table."""
        lines = [
            "| Rank | Config | Time (s) | Fitness | Security | Transforms |",
            "|------|--------|----------|---------|----------|------------|",
        ]
        for i, (config, result) in enumerate(ranked[:10]):
            fitness_val = self._fitness(result)
            transforms = ", ".join(t.replace("_", " ") for t in config.transforms)
            lines.append(
                f"| {i+1} | {config.name} | {result.time_seconds:.1f} | "
                f"{fitness_val:.4f} | {result.security_bits} | {transforms} |"
            )
        return "\n".join(lines)
    
    def _fitness(self, result) -> float:
        if not result.correctness or result.time_seconds < 0:
            return 0.0
        speed_score = 1.0 / result.time_seconds if result.time_seconds > 0 else 0
        speed_score = speed_score * 1000
        memory_penalty = min(result.memory_mb / 1000.0, 1.0) * 0.1
        security_factor = result.security_bits / 128.0
        return speed_score * (1.0 - memory_penalty) * security_factor
    
    def build_prompt(self, ranked: list[tuple], iteration: int) -> str:
        """Build the LLM prompt for proposing new candidates."""
        results_table = self.format_results_table(ranked)
        
        # Identify patterns
        top_transforms = {}
        for config, result in ranked[:5]:
            for t in config.transforms:
                top_transforms[t] = top_transforms.get(t, 0) + 1
        
        helpful = [t for t, c in top_transforms.items() if c >= 3]
        
        prompt = f"""## SR PRP Optimization Search - Iteration {iteration + 1}

### Problem Context
We're optimizing a Swap-or-Not Sometimes-Recurse PRP implementation.
Current bottleneck: ~770 AES rounds per SR level with 128-bit security.
Goal: Reduce hint generation time from ~50 min to <5 min (10x speedup).

### Available Transforms
- T1_PRECOMPUTE_KEYS: Cache round keys at construction (already applied to all)
- T2_BATCH_AES: Process multiple AES blocks in parallel via AES-NI
- T3_LAZY_SR: Skip deep SR levels when value exits early
- T4_SIMD_PRF: Vectorize prf_bit computation with SIMD
- T5_ROUND_UNROLL: Unroll inner round loop (factor: 2, 4, or 8)
- T6_CACHE_CANONICAL: Memoize canonical representative computations
- T7_REDUCED_SECURITY: Allow security_bits < 128

### Available Parameters
- security_bits: [32, 64, 80, 96, 128]
- batch_size: [1, 2, 4, 8, 16]
- unroll_factor: [2, 4, 8]

### Current Results
{results_table}

### Patterns Observed
- Transforms that appear in top 5: {helpful if helpful else "None yet"}
- Best time so far: {ranked[0][1].time_seconds:.1f}s
- Best config: {ranked[0][0].name}

### Task
Propose 3 new candidate configurations. For each, provide:
1. A unique name (prefix with "evo_iter{iteration+1}_")
2. List of transforms to apply
3. Parameter values
4. Brief reasoning

Focus on:
- Unexplored combinations of transforms
- Parameter tuning of successful configs
- Balancing speed vs security tradeoffs

Respond in JSON format:
```json
[
  {{
    "name": "evo_iter{iteration+1}_example",
    "transforms": ["T1_PRECOMPUTE_KEYS", "T2_BATCH_AES"],
    "params": {{"security_bits": 64, "batch_size": 8}},
    "description": "Reasoning here"
  }}
]
```
"""
        return prompt
    
    def parse_llm_response(self, response: str, iteration: int) -> list[CandidateConfig]:
        """Parse LLM response into candidate configs."""
        # Extract JSON from response
        try:
            # Find JSON array in response
            start = response.find("[")
            end = response.rfind("]") + 1
            if start >= 0 and end > start:
                json_str = response[start:end]
                proposals = json.loads(json_str)
                
                configs = []
                for p in proposals:
                    # Validate transforms
                    transforms = [t for t in p.get("transforms", []) if t in AVAILABLE_TRANSFORMS]
                    if not transforms:
                        transforms = ["T1_PRECOMPUTE_KEYS"]
                    
                    # Validate params
                    params = p.get("params", {})
                    if "security_bits" not in params:
                        params["security_bits"] = 128
                    if "batch_size" not in params:
                        params["batch_size"] = 1
                    
                    configs.append(CandidateConfig(
                        name=p.get("name", f"evo_iter{iteration+1}_{self.proposal_count}"),
                        transforms=transforms,
                        params=params,
                        description=p.get("description", "")
                    ))
                    self.proposal_count += 1
                
                return configs
        except (json.JSONDecodeError, KeyError, TypeError) as e:
            print(f"  Warning: Failed to parse LLM response: {e}")
        
        return []
    
    def propose_fallback(self, ranked: list[tuple], iteration: int) -> list[CandidateConfig]:
        """Fallback proposal strategy when LLM is unavailable."""
        proposals = []
        
        # Strategy 1: Mutate best performer
        if ranked:
            best_config, _ = ranked[0]
            mutated_params = dict(best_config.params)
            
            # Random mutation
            if random.random() < 0.5 and mutated_params.get("batch_size", 1) < 16:
                mutated_params["batch_size"] = min(mutated_params.get("batch_size", 1) * 2, 16)
            elif mutated_params.get("security_bits", 128) > 32:
                idx = PARAM_RANGES["security_bits"].index(mutated_params.get("security_bits", 128))
                if idx > 0:
                    mutated_params["security_bits"] = PARAM_RANGES["security_bits"][idx - 1]
            
            proposals.append(CandidateConfig(
                name=f"evo_iter{iteration+1}_mutate_{self.proposal_count}",
                transforms=list(best_config.transforms),
                params=mutated_params,
                description="Mutation of best performer"
            ))
            self.proposal_count += 1
        
        # Strategy 2: Add new transform to best
        if ranked:
            best_config, _ = ranked[0]
            unused = [t for t in AVAILABLE_TRANSFORMS if t not in best_config.transforms]
            if unused:
                new_transform = random.choice(unused)
                new_transforms = list(best_config.transforms) + [new_transform]
                new_params = dict(best_config.params)
                if new_transform == "T5_ROUND_UNROLL":
                    new_params["unroll_factor"] = 4
                
                proposals.append(CandidateConfig(
                    name=f"evo_iter{iteration+1}_add_{self.proposal_count}",
                    transforms=new_transforms,
                    params=new_params,
                    description=f"Add {new_transform} to best"
                ))
                self.proposal_count += 1
        
        # Strategy 3: Crossover of top 2
        if len(ranked) >= 2:
            config1, _ = ranked[0]
            config2, _ = ranked[1]
            
            # Combine transforms
            combined_transforms = list(set(config1.transforms) | set(config2.transforms))
            
            # Average params
            combined_params = {
                "security_bits": min(config1.params.get("security_bits", 128),
                                    config2.params.get("security_bits", 128)),
                "batch_size": max(config1.params.get("batch_size", 1),
                                 config2.params.get("batch_size", 1)),
            }
            
            proposals.append(CandidateConfig(
                name=f"evo_iter{iteration+1}_cross_{self.proposal_count}",
                transforms=combined_transforms,
                params=combined_params,
                description="Crossover of top 2"
            ))
            self.proposal_count += 1
        
        return proposals
    
    def propose(self, ranked: list[tuple], iteration: int) -> list[CandidateConfig]:
        """Generate new candidate proposals."""
        if self.client:
            print("  Consulting LLM for proposals...")
            prompt = self.build_prompt(ranked, iteration)
            
            try:
                response = self.client.messages.create(
                    model="claude-sonnet-4-20250514",
                    max_tokens=2000,
                    messages=[{"role": "user", "content": prompt}]
                )
                
                response_text = response.content[0].text
                proposals = self.parse_llm_response(response_text, iteration)
                
                if proposals:
                    print(f"  LLM proposed {len(proposals)} candidates")
                    for p in proposals:
                        print(f"    - {p.name}: {p.transforms}")
                    return proposals
            except Exception as e:
                print(f"  LLM call failed: {e}")
        
        # Fallback to heuristic proposals
        print("  Using fallback proposal strategy...")
        return self.propose_fallback(ranked, iteration)


if __name__ == "__main__":
    # Test the proposer
    proposer = LLMProposer()
    
    # Mock ranked results
    @dataclass
    class MockResult:
        time_seconds: float
        throughput_entries_per_sec: float
        memory_mb: float
        correctness: bool
        security_bits: int
    
    mock_ranked = [
        (CandidateConfig("test1", ["T1_PRECOMPUTE_KEYS"], {"security_bits": 128}),
         MockResult(100, 10, 50, True, 128)),
        (CandidateConfig("test2", ["T1_PRECOMPUTE_KEYS", "T2_BATCH_AES"], {"security_bits": 64, "batch_size": 8}),
         MockResult(80, 12, 60, True, 64)),
    ]
    
    proposals = proposer.propose(mock_ranked, 0)
    print(f"\nGenerated {len(proposals)} proposals:")
    for p in proposals:
        print(f"  {p.name}: {p.transforms} {p.params}")
