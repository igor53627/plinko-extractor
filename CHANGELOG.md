# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- **TEE constant-time exact binomial sampler** (`binomial_sample_tee`): Issue #41 fix
  - True Binomial(n,p) distribution using inverse-CDF with fixed iterations
  - O(CT_BINOMIAL_MAX_COUNT) complexity with constant-time float comparison and selection
  - No branches depend on `count` or `prf_output` (both treated as secret)
  - Uses log-gamma mode-based computation for numerical stability (supports n up to ~40k)
  - Uses `ct_f64_le`, `ct_select_f64` for constant-time IEEE 754 float operations
  - Threshold: `count <= CT_BINOMIAL_MAX_COUNT` (65536); no fallback - approximation removed entirely
  - `IprfTee` now uses `binomial_sample_tee` for TEE-safe execution
  - `IprfTee::new` asserts `n <= CT_BINOMIAL_MAX_COUNT` to enforce protocol invariant
  - `IprfTee::inverse_ct` uses constant-time min for MAX_PREIMAGES clamping
  - Non-TEE `Iprf` continues to use standard binomial sampler
- **Sometimes-Recurse PRP** (`SwapOrNotSr`, `SwapOrNotSrTee`): Morris-Rogaway Fig. 1 wrapper for full-domain security
  - Level-aware key derivation with proper domain separation
  - Paper-faithful round counts: `t_N = ceil(7.23 lg N + 4.82 lambda + 4.82 lg p)` per Morris-Rogaway Eq. (2)
  - Configurable security parameter (default 128-bit)
  - `with_security(key, domain, security_bits)` constructor for explicit security level
- **Constant-time utilities**: Added `ct_ge_u64` for branchless greater-or-equal comparison
- **Formal verification**: `SwapOrNotSrSpec.v` with Rocq proofs for SR round involution, range preservation, and bijection properties
- **Documentation**: Alex Hoover talk transcript explaining full-domain PRP requirement for Plinko hint reuse security
- Seed-based subset derivation functions (`derive_subset_seed`, `compute_regular_blocks`, `compute_backup_blocks`)
- New unit tests for subset seed derivation and block computation
- CI improvements:
  - `OPAMJOBS=2` for parallel Rocq compilation
  - Better cache keys with Makefile hash and versioning (v2)
  - Conditional opam setup (skip if cached)
  - `ci-quick` / `ci-full` targets for PR vs main builds
  - Audit artifacts upload
  - GitHub step summary with verification table
  - `admit-count` and `verify-axioms` Makefile targets
  - Configurable `COQC`/`COQDEP` (avoids symlink brittleness)

### Changed

- **iPRF**: `Iprf` and `IprfTee` now use `SwapOrNotSr`/`SwapOrNotSrTee` instead of plain `SwapOrNot` for full-domain security
- **Hint storage**: Hints now store a 32-byte seed instead of explicit block lists, significantly reducing memory footprint
- **Block count (c)**: Auto-bumped to even if odd (required for security proof); hard assertion enforced in production mode
- **Padding**: Replace `find_nearest_divisor` with padding - DB is padded with dummy zero entries instead of truncating tail entries
- **CLI**: `--allow-truncation` is now hidden (debug-only flag that violates security assumptions)
- **CLI docs**: Fixed description for `--entries-per-block` to reflect padding behavior

### Fixed

- **SR round counts**: Implemented paper-faithful per-stage epsilon-budget schedule (Morris-Rogaway Section 5, Strategy 1) for provable 128-bit security; previous heuristic had no proven bound
- Block count evenness now properly enforced for Plinko security proof compliance
