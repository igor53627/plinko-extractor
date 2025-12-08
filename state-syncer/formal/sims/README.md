# Simulation Layer for Plinko Verification

This directory contains simulation relations connecting Rocq specifications (in `specs/`) to translated Rust code.

## Overview

The simulation layer establishes refinement relations proving that Rust implementations correctly implement their Rocq specifications.

```
specs/           Rocq specifications (pure functional)
    |
    | simulation relations (this directory)
    v
src/ (future)    Translated Rust code (from rocq-of-rust)
```

## Prerequisites

1. **rocq-of-rust**: Translate Rust code to Rocq
   - Repository: https://github.com/formal-land/coq-of-rust
   - Translates `state-syncer/src/*.rs` to Rocq definitions

2. **Specs must compile**: Run `make specs` in parent directory first

## Approach

### 1. Refinement Relations

Define relations `R : RustType -> SpecType -> Prop` establishing when Rust values correctly represent spec values:

- `refines_u64`: Rust u64 refines Z when in range [0, 2^64)
- `refines_list`: Element-wise refinement for lists
- `refines_swap_or_not`: SwapOrNot state refinement
- `refines_iprf`: IPRF state refinement

### 2. Forward Simulation

For each function, prove:
```
forall rust_in spec_in rust_out spec_out,
  R_in rust_in spec_in ->
  rust_fn rust_in = rust_out ->
  spec_fn spec_in = spec_out ->
  R_out rust_out spec_out
```

### 3. Property Lifting

Once simulation is established, lift spec properties to Rust:
- If spec satisfies property P, and Rust refines spec, then Rust satisfies P

## Files

| File | Purpose |
|------|---------|
| `SimTypes.v` | Refinement relation definitions |
| `SwapOrNotSim.v` (TODO) | SwapOrNot simulation proofs |
| `IprfSim.v` (TODO) | IPRF simulation proofs |
| `PlinkoSim.v` (TODO) | Full Plinko simulation |

## Building

```bash
cd /Users/user/pse/plinko-extractor/state-syncer/formal
coqc -Q specs Plinko.Specs -Q sims Plinko.Sims sims/SimTypes.v
```

Or use the Makefile:
```bash
make sims
```

## TODO

1. Set up rocq-of-rust translation pipeline
2. Import translated Rust definitions
3. Complete refinement relations for domain types
4. Prove simulation for each function
5. Lift security properties from specs to Rust
