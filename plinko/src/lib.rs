//! Plinko PIR library
//!
//! This crate provides core Plinko PIR primitives:
//! - `iprf`: Invertible PRF implementation (paper §4.2)
//! - `db`: Database loading and Plinko parameter derivation
//! - `constant_time`: Data-oblivious operations for TEE execution
//! - `binomial`: True derandomized binomial sampling for PMNS
//! - `binomial_tee`: Parameterized TEE sampler with configurable iteration bounds

pub mod binomial;
pub mod binomial_gaussian;
pub mod binomial_leveled;
pub mod binomial_precomputed;
pub mod binomial_tee;
pub mod constant_time;
pub mod db;
pub mod iprf;

#[cfg(any(kani, test))]
#[path = "kani_proofs.rs"]
mod kani_proofs;
