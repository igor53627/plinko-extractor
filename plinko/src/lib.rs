//! Plinko PIR Library
//!
//! Core components for the Plinko Private Information Retrieval scheme:
//! - `iprf`: Invertible PRF implementation (Swap-or-Not PRP + PMNS)
//! - `db`: Database loading and Plinko parameter derivation
//! - `constant_time`: TEE-safe constant-time operations

pub mod constant_time;
pub mod db;
pub mod iprf;

#[cfg(any(kani, test))]
#[path = "kani_proofs.rs"]
mod kani_proofs;
