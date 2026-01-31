//! RIINA Language Server Protocol
//!
//! Hand-written JSON-RPC over stdio for zero-dependency LSP.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

#![forbid(unsafe_code)]

pub mod json;
pub mod jsonrpc;
pub mod server;
pub mod analysis;
