//! State Syncer library for Plinko PIR
//!
//! This crate provides core Plinko PIR primitives:
//! - `iprf`: Invertible PRF implementation (paper §4.2)
//! - `db`: Database loading and Plinko parameter derivation
//! - `constant_time`: Data-oblivious operations for TEE execution

pub mod constant_time;
pub mod db;
pub mod iprf;

#[cfg(any(kani, test))]
#[path = "kani_proofs.rs"]
mod kani_proofs;
