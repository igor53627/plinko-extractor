# Plinko Extractor - Agent Rules

## Canonical Protocol Reference

**`docs/plinko_paper_index.json`** is the canonical source of truth for Plinko protocol implementation details. It indexes:
- Parsed paper content (`plinko_paper_part*.json`)
- Regression test data location (Cloudflare R2)
- Video resources
- Agent usage notes for different tasks

Always consult this file first when implementing or verifying protocol logic.

## Host: root@aya

- **Reth DB location**: `/mnt/mainnet/data`
- **Working directory**: `/mnt/mainnet/plinko`
- **DO NOT** create artifacts outside `/mnt/mainnet/plinko` without explicit user permission

## Build Commands

```bash
# Build extractor
cargo build --release

# Build hints generator
cd state-syncer && cargo build --release --bin plinko_hints
```

## Run Commands

```bash
# Extract from Reth DB (on aya)
./target/release/plinko-extractor \
  --db-path /mnt/mainnet/data \
  --output-dir /mnt/mainnet/plinko

# Generate hints (standard mode)
./state-syncer/target/release/plinko_hints \
  --db-path /mnt/mainnet/plinko/database.bin \
  --lambda 128

# Generate hints (XOF mode - faster)
./state-syncer/target/release/plinko_hints \
  --db-path /mnt/mainnet/plinko/database.bin \
  --lambda 128 --xof
```

## Data Format

- Accounts: 3 words (96 bytes) - nonce, balance, bytecode_hash
- Storage: 1 word (32 bytes) - value

## Style

- Do NOT use emojis in code, comments, or documentation

## Formal Verification Compliance

When modifying Rust code in `state-syncer/`, ALWAYS verify changes don't break alignment with:

1. **Paper specification** (`docs/plinko_paper_*.json`)
   - HintInit must match Fig. 7 pseudocode
   - iPRF domain/range must be correct (domain=num_hints, range=w)
   - Key generation: one iPRF key per block

2. **Coq specification** (`docs/Plinko.v`)
   - `RegularHint`: block subset of c/2+1, single parity
   - `BackupHint`: block subset of c/2, dual parities (in/out)
   - `hint_init`, `process_db_entry` logic must match

3. **Rocq proofs** (`plinko/formal/`)
   - `specs/*.v`: iPRF, SwapOrNot, binomial specs
   - `proofs/*.v`: Verified properties
   - Do NOT change Rust semantics that would invalidate proofs

### Verification Checklist

Before committing Rust changes to hint generation or iPRF:

- [ ] iPRF instantiation: `Iprf::new(key, domain, range)` where domain=total_hints, range=w
- [ ] Per-block keys: c keys derived from master seed
- [ ] Regular hints: subset size c/2+1, single parity XOR'd when block in P
- [ ] Backup hints: subset size c/2, parity_in when block in P, parity_out otherwise
- [ ] Streaming: (block, offset) = (i/w, i mod w), use block's key for iPRF.inverse(offset)

### Reference Files

| Spec | Location |
|------|----------|
| Paper HintInit | `docs/plinko_paper_part6_algorithms.json` (algorithm_id: plinko_hintinit) |
| Coq HintInit | `docs/Plinko.v` (hint_init, process_db_entry) |
| iPRF Spec | `plinko/formal/specs/IprfSpec.v` |
| PRP Spec | `plinko/formal/specs/SwapOrNotSpec.v` |

## Devin DeepWiki

Update `.devin/wiki.json` when making changes worth documenting:
- Add repo_notes for new features, data locations, or architectural changes
- Update pages array if new components need dedicated documentation
- DeepWiki regenerates on next Devin indexing
