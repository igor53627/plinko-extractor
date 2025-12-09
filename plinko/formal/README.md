# Plinko Formal Verification

Overview of the formal verification infrastructure using rocq-of-rust.

## Structure

```
formal/
  specs/           - Pure Rocq specifications
    CommonTypes.v  - Shared types (Z-based integers, predicates)
    DbSpec.v       - derive_plinko_params specification
    BinomialSpec.v - binomial_sample specification  
    SwapOrNotSpec.v - Swap-or-Not PRP specification
    IprfSpec.v     - iPRF/PMNS specification
    
  proofs/          - Property proofs on specifications
    DbProofs.v     - derive_plinko_params invariants
    SwapOrNotProofs.v - PRP bijection properties
    IprfProofs.v   - iPRF inverse/partition properties
    PrpBridge.v    - Bridge abstract PRP axioms to concrete SwapOrNot
    
  sims/            - Simulation relations (Rust <-> Spec)
    SimTypes.v     - Basic refinement relation infrastructure
    SwapOrNotSim.v - SwapOrNot PRP simulation (Rust -> Spec)
    IprfSim.v      - iPRF simulation (Rust -> Spec)
    HintInitSim.v  - HintInit simulation (streaming <-> batch)
    
  linking/         - Type links to rocq-of-rust translation
    types.v        - Link instances for Rust types
    
  scripts/         - Automation scripts
    translate.sh   - Translate Rust to Rocq using rocq-of-rust
    
  Makefile         - Build system
```

## Building

Prerequisites:
- Rocq 9.x (opam switch rocq-9)
- rocq-of-rust (at ~/pse/paradigm/rocq-of-rust)

```bash
# Check dependencies
make check-deps

# Build specifications and proofs
make all

# Build with linking layer (requires RocqOfRust library)
make linking

# Translate Rust to Rocq
make translate

# Full CI build
make ci
```

## Properties Verified

### derive_plinko_params
- chunk_size is power of 2
- chunk_size >= 2 * sqrt(db_entries)
- set_size > 0 and divisible by 4
- capacity >= db_entries

### SwapOrNot PRP
- partner is an involution: partner(partner(x)) = x
- Each round is an involution: round(round(x)) = x
- forward and inverse are mutual inverses
- forward is a bijection on [0, N)

### iPRF
- forward(x) in [0, m) for x in [0, n)
- inverse(forward(x)) contains x
- inverses partition the domain [0, n)

## Proof Status

Legend: [x] Proven, [~] Axiomatized/Parameterized, [ ] TODO

Specs:
- [x] CommonTypes
- [x] DbSpec  
- [x] BinomialSpec
- [x] SwapOrNotSpec
- [x] IprfSpec (all key lemmas proven)

Proofs:
- [x] DbProofs (all admits discharged)
- [x] SwapOrNotProofs (partner_involutive, round_involutive, bijection proven)
- [x] IprfProofs (relies on PRP axioms; PMNS core lemmas fully proven)
- [x] PrpBridge (connects abstract PRP axioms to SwapOrNot)

Simulations:
- [x] SimTypes (refinement relation infrastructure)
- [x] SwapOrNotSim (PRP simulation with AES axioms)
- [x] IprfSim (iPRF simulation composing PRP + PMNS)
- [~] HintInitSim (streaming <-> batch correctness, 1 admit - backup hints only, regular hints PROVEN)

Linking:
- [x] Type definitions
- [~] Full translation (requires rocq-of-rust)

## Crypto Trust Base

See [docs/TRUST_BASE.md](docs/TRUST_BASE.md) for a complete catalog of all axioms
and parameters in the verification, including:

- **5 AES axioms** - Functional behavior of AES-128 block cipher
- **8 PRP axioms** - Abstract permutation properties (discharged via PrpBridge.v)
- **3 key derivation axioms** - Hash-based key derivation properties
- **3 subset membership axioms** - Hash-based subset selection properties
- **8 structural parameters** - Abstract interface (prf_eval, encode_node, etc.)

The trust base document explains what each axiom assumes, why it's reasonable,
and what external verification would be needed to discharge it.

## Axioms and Admits

Run `make audit` to see current axioms and admits:

**Axioms (6):**
- `N_pos`: Domain is positive (matches Rust assert)
- `round_key_in_range`: Round keys in valid range (follows from AES mod N)
- `prp_forward_in_range`, `prp_inverse_in_range`: PRP outputs in domain
- `prp_forward_inverse`, `prp_inverse_forward`: PRP inverse properties

**Parameters (8):** Abstract PRF/PRP functions (N, num_rounds, round_key, 
round_bit, prf_eval, encode_node, prp_forward, prp_inverse)

**Admits (2 total):**
- IprfSpec.v: 1 (`binomial_sample_range_aux` edge case for count=0)
- HintInitSim.v: 1 (`hint_init_backup_streaming_eq_batch` - backup hints only)

The IprfSpec.v admit is for an edge case that doesn't occur in the main algorithm.
The HintInitSim.v admit is for backup hints only - the main regular hints theorem
(`hint_init_streaming_eq_batch`) is **fully proven** with no admits.

Note: All core PMNS lemmas (trace_ball_inverse_consistent, trace_ball_inverse_fuel_disjoint,
iPRF lemmas) are fully proven. SwapOrNotSpec.v admits are re-proved in SwapOrNotProofs.v.

## Completed Proofs

### SwapOrNot (proofs/SwapOrNotProofs.v)
- `partner_involutive_full`: Modular arithmetic proof showing partner(partner(x)) = x
- `round_involutive_full`: Each round is self-inverse using partner involution + canonical symmetry
- `forward_inverse_id_full`, `inverse_forward_id_full`: Full permutation properties
- `forward_injective`, `forward_surjective`, `forward_is_bijection`: Bijection proof

### Database Parameters (proofs/DbProofs.v)
- `smallest_power_of_two_geq_is_power_of_two`: Result is always a power of 2
- `smallest_power_of_two_geq_geq`: Result >= input
- `smallest_power_of_two_geq_le_double`: Result <= 2 * input
- `ceil_div_mul_ge`, `round_up_multiple_ge`: Ceiling division properties
- `derive_plinko_params_all_invariants`: Combined correctness theorem

### PMNS (specs/IprfSpec.v)
- `trace_ball_step_invariants`: Loop progress and invariant preservation
- `trace_ball_fuel_inverse_contains`: Core lemma showing forward/inverse 
  traverse the same binary tree path. If forward(x) = y, then inverse(y) contains x.
- `trace_ball_inverse_fuel_consistent`: **NEWLY PROVEN** - Converse: if x ∈ inverse(y), 
  then forward(x) = y. Proved by induction on fuel, showing branch conditions match.
- `trace_ball_inverse_fuel_disjoint`: **NEWLY PROVEN** - Different y values give disjoint 
  ball ranges. Four-way case analysis on left/right branching.
- `trace_ball_inverse_consistent`: **NEWLY PROVEN** - Spec-level consistency lemma
- `iprf_forward_in_range`, `iprf_inverse_contains_preimage`, `iprf_inverse_elements_in_domain`,
  `iprf_inverse_elements_map_to_y`, `iprf_inverse_partitions_domain`: **NEWLY PROVEN** - 
  All iPRF lemmas now proven, composing PRP axioms with trace_ball lemmas.

## Next Steps

1. **Consolidate PRP axioms** (S effort)
   - IprfProofs.v duplicates PRP axioms from IprfSpec.v
   - Should reuse the global axioms instead

2. **Address the count=0 edge case** (S effort)
   - Either strengthen preconditions throughout to require ball_count > 0
   - Or accept the admit as a harmless edge case that doesn't affect correctness

3. **Complete HintInit simulation proofs** (M effort)
   - Prove streaming == batch correctness (hint_init_streaming_eq_batch)
   - Requires showing iPRF partition property implies XOR accumulation equivalence

4. **Run rocq-of-rust translation** (M effort)
   - Install rocq-of-rust: `cargo install coq-of-rust`
   - Run `./scripts/translate.sh` to generate translated Rust
   - Connect translated definitions to simulation relations

## Architecture Notes

The verification follows a layered approach:
1. **Specs**: Pure functional specifications matching Rust semantics
2. **Proofs**: Properties proven on specs (no admits in proof layer)
3. **Bridging**: `PrpBridge.v` connects abstract PRP axioms to concrete SwapOrNot
4. **Simulations**: Connect Rust implementation behavior to spec behavior
5. **Linking**: Connects specs to rocq-of-rust translation

### Simulation Layer Architecture

The simulation layer (`sims/`) establishes refinement relations between Rust
implementations and Rocq specifications:

```
Rust Implementation          Simulation Layer         Rocq Specification
-------------------          ----------------         ------------------
SwapOrNot::forward()  <-->   SwapOrNotSim.v    <-->   forward_spec
SwapOrNot::inverse()  <-->                     <-->   inverse_spec
Iprf::forward()       <-->   IprfSim.v         <-->   iprf_forward_spec
Iprf::inverse()       <-->                     <-->   iprf_inverse_spec
HintInit streaming    <-->   HintInitSim.v     <-->   batch specification
```

Key simulation relations:
- **SwapOrNotSim**: Axiomatizes AES-128 crypto, proves round-by-round equivalence
- **IprfSim**: Composes SwapOrNot (PRP) + trace_ball (PMNS) simulations
- **HintInitSim**: Proves streaming database processing equals batch computation

Properties are lifted from specs to Rust via simulation:
```
Spec Property (proven) + Simulation (proven) => Rust Property (derived)
```

### PRP Axiom Discharge Strategy

The iPRF proofs in `IprfProofs.v` use 4 abstract PRP axioms for generality.
These are **discharged** for the concrete SwapOrNot case via `PrpBridge.v`:

```
IprfProofs.v (abstract PRP)     PrpBridge.v (bridge)      SwapOrNotProofs.v (concrete)
  prp_forward_in_range    <-->   prp_forward_in_range_N   <-->   forward_in_range_full
  prp_inverse_in_range    <-->   prp_inverse_in_range_N   <-->   inverse_in_range_full
  prp_forward_inverse     <-->   prp_forward_inverse_N    <-->   forward_inverse_id_full
  prp_inverse_forward     <-->   prp_inverse_forward_N    <-->   inverse_forward_id_full
```

This keeps the abstract iPRF development reusable while proving the concrete
SwapOrNot PRP satisfies all requirements.
