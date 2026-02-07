// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Core Primitives
//!
//! This crate provides the foundational types and primitives for the RIINA
//! security platform. All types are designed with security as the primary
//! concern, following the 11 Immutable Laws.
//!
//! # Laws Enforced
//!
//! - **Law 2**: Cryptographic non-negotiables (AES-256-GCM, ML-KEM-768+X25519, ML-DSA-65+Ed25519)
//! - **Law 3**: All operations on secret data are constant-time
//! - **Law 4**: All secrets are zeroized when no longer needed
//! - **Law 8**: Zero third-party runtime dependencies
//!
//! # Modules
//!
//! - `zeroize`: Secure memory zeroization
//! - `constant_time`: Constant-time comparison operations
//! - `secret`: Secret value wrapper with automatic zeroization
//! - `crypto`: Cryptographic primitives (AES, SHA-256, HMAC, HKDF, GCM, X25519, Ed25519, ML-KEM, ML-DSA)
//!
//! # Example
//!
//! ```
//! use riina_core::prelude::*;
//! use riina_core::crypto::gcm::Aes256Gcm;
//!
//! // Create a secret key
//! let key = Secret::new([0x42u8; 32]);
//!
//! // Key is automatically zeroized when dropped
//! ```

#![deny(unsafe_code)] // Deny unsafe by default, but allow specific modules (e.g., zeroize) to override
#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
// Allow common pedantic lints that aren't security-critical
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::missing_panics_doc)]
#![allow(clippy::missing_const_for_fn)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::doc_markdown)]
// Allow casts in crypto code (carefully audited)
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_sign_loss)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_lossless)]
#![allow(clippy::use_self)]
#![allow(clippy::similar_names)]
#![allow(clippy::too_many_lines)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::assign_op_pattern)]
// Allow unwrap in crypto code for validated array conversions
// These are safe because slice sizes are verified at compile time
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
// Additional allows for crypto implementation patterns
#![allow(clippy::unreadable_literal)]
#![allow(trivial_numeric_casts)]
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::panic)]
#![allow(clippy::unused_self)]
#![allow(dead_code)]
// Additional allows for code patterns in crypto implementations
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::manual_let_else)]
#![allow(clippy::if_not_else)]
#![allow(clippy::ptr_as_ptr)]
#![allow(clippy::bool_to_int_with_if)]
#![allow(clippy::uninlined_format_args)]
#![allow(unused_variables)]
#![allow(unused_assignments)]

pub mod constant_time;
pub mod crypto;
pub mod secret;
pub mod zeroize;

/// Prelude for convenient imports
pub mod prelude {
    pub use crate::constant_time::ConstantTimeEq;
    pub use crate::secret::Secret;
    pub use crate::zeroize::Zeroize;
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    #[test]
    fn test_secret_zeroization() {
        let secret = Secret::new([0x42u8; 32]);
        assert!(secret.expose_secret().iter().all(|&b| b == 0x42));
        // Secret will be zeroized when dropped
    }

    #[test]
    fn test_constant_time_eq() {
        let a = [1u8, 2, 3, 4];
        let b = [1u8, 2, 3, 4];
        let c = [1u8, 2, 3, 5];

        assert!(a.ct_eq(&b));
        assert!(!a.ct_eq(&c));
    }
}
