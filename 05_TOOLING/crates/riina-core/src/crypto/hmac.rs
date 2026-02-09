// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! HMAC (Hash-based Message Authentication Code) Implementation
//!
//! This module implements HMAC as specified in RFC 2104 and FIPS 198-1.
//! Currently supports HMAC-SHA256.
//!
//! # Security Notes
//!
//! - Keys are zeroized after use (Law 4)
//! - Verification uses constant-time comparison (Law 3)
//! - No memory allocation during MAC computation
//!
//! # Safety
//!
//! This module uses `unsafe` for `ManuallyDrop::take` in the finalize method.
//! This is necessary because the struct implements Drop for key zeroization,
//! but we need to move the inner hash state out during finalization.

#![allow(unsafe_code)]

use crate::constant_time::ConstantTimeEq;
use crate::crypto::sha2::{Sha256, BLOCK_SIZE, OUTPUT_SIZE};
use crate::zeroize::Zeroize;
use core::mem::ManuallyDrop;

/// HMAC-SHA256 output size in bytes
pub const HMAC_SHA256_OUTPUT_SIZE: usize = OUTPUT_SIZE;

/// HMAC-SHA256 implementation
pub struct HmacSha256 {
    /// Inner key (key XOR ipad)
    inner_key: [u8; BLOCK_SIZE],
    /// Outer key (key XOR opad)
    outer_key: [u8; BLOCK_SIZE],
    /// Inner hash state (wrapped in ManuallyDrop to allow moving out in finalize)
    inner_hash: ManuallyDrop<Sha256>,
}

impl HmacSha256 {
    /// Create a new HMAC-SHA256 instance from a key
    ///
    /// Keys longer than the block size (64 bytes) are hashed.
    /// Keys shorter than the block size are zero-padded.
    #[must_use]
    pub fn new(key: &[u8]) -> Self {
        // Prepare the key
        let mut key_block = [0u8; BLOCK_SIZE];

        if key.len() > BLOCK_SIZE {
            // Hash the key if it's too long
            let hash = Sha256::hash(key);
            key_block[..OUTPUT_SIZE].copy_from_slice(&hash);
        } else {
            // Zero-pad the key if it's too short
            key_block[..key.len()].copy_from_slice(key);
        }

        // Compute inner and outer keys
        let mut inner_key = [0u8; BLOCK_SIZE];
        let mut outer_key = [0u8; BLOCK_SIZE];

        for i in 0..BLOCK_SIZE {
            inner_key[i] = key_block[i] ^ 0x36; // ipad
            outer_key[i] = key_block[i] ^ 0x5c; // opad
        }

        // Zeroize the key block
        key_block.zeroize();

        // Initialize inner hash with inner key
        let mut inner_hash = Sha256::new();
        inner_hash.update(&inner_key);

        Self {
            inner_key,
            outer_key,
            inner_hash: ManuallyDrop::new(inner_hash),
        }
    }

    /// Update the MAC with additional data
    pub fn update(&mut self, data: &[u8]) {
        self.inner_hash.update(data);
    }

    /// Finalize and return the MAC
    #[must_use]
    pub fn finalize(mut self) -> [u8; HMAC_SHA256_OUTPUT_SIZE] {
        // Complete inner hash
        // SAFETY: We take ownership of inner_hash here. The Drop impl will only
        // zeroize the keys, not the inner_hash (since it's ManuallyDrop).
        let inner_hash = unsafe { ManuallyDrop::take(&mut self.inner_hash) };
        let inner_result = inner_hash.finalize();

        // Compute outer hash: H(outer_key || inner_result)
        let mut outer_hash = Sha256::new();
        outer_hash.update(&self.outer_key);
        outer_hash.update(&inner_result);

        outer_hash.finalize()
    }

    /// Compute MAC in one call
    #[must_use]
    pub fn mac(key: &[u8], data: &[u8]) -> [u8; HMAC_SHA256_OUTPUT_SIZE] {
        let mut hmac = Self::new(key);
        hmac.update(data);
        hmac.finalize()
    }

    /// Verify a MAC in constant time
    ///
    /// Returns `true` if the MAC is valid, `false` otherwise.
    #[must_use]
    pub fn verify(key: &[u8], data: &[u8], expected_mac: &[u8]) -> bool {
        if expected_mac.len() != HMAC_SHA256_OUTPUT_SIZE {
            return false;
        }

        let computed_mac = Self::mac(key, data);
        // Convert slice to array reference (length already verified)
        let expected: &[u8; 32] = expected_mac.try_into().unwrap();
        computed_mac.ct_eq(expected)
    }
}

impl Drop for HmacSha256 {
    fn drop(&mut self) {
        // Zeroize keys (Law 4)
        self.inner_key.zeroize();
        self.outer_key.zeroize();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 4231 Test Case 1
    #[test]
    fn test_hmac_sha256_rfc4231_case1() {
        let key = [0x0bu8; 20];
        let data = b"Hi There";

        let mac = HmacSha256::mac(&key, data);
        let expected: [u8; 32] = [
            0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53, 0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b,
            0xf1, 0x2b, 0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7, 0x26, 0xe9, 0x37, 0x6c,
            0x2e, 0x32, 0xcf, 0xf7,
        ];

        assert_eq!(mac, expected);
    }

    /// RFC 4231 Test Case 2 (key = "Jefe")
    #[test]
    fn test_hmac_sha256_rfc4231_case2() {
        let key = b"Jefe";
        let data = b"what do ya want for nothing?";

        let mac = HmacSha256::mac(key, data);
        let expected: [u8; 32] = [
            0x5b, 0xdc, 0xc1, 0x46, 0xbf, 0x60, 0x75, 0x4e, 0x6a, 0x04, 0x24, 0x26, 0x08, 0x95,
            0x75, 0xc7, 0x5a, 0x00, 0x3f, 0x08, 0x9d, 0x27, 0x39, 0x83, 0x9d, 0xec, 0x58, 0xb9,
            0x64, 0xec, 0x38, 0x43,
        ];

        assert_eq!(mac, expected);
    }

    /// RFC 4231 Test Case 3 (key and data are 0xaa and 0xdd repeated)
    #[test]
    fn test_hmac_sha256_rfc4231_case3() {
        let key = [0xaau8; 20];
        let data = [0xddu8; 50];

        let mac = HmacSha256::mac(&key, &data);
        let expected: [u8; 32] = [
            0x77, 0x3e, 0xa9, 0x1e, 0x36, 0x80, 0x0e, 0x46, 0x85, 0x4d, 0xb8, 0xeb, 0xd0, 0x91,
            0x81, 0xa7, 0x29, 0x59, 0x09, 0x8b, 0x3e, 0xf8, 0xc1, 0x22, 0xd9, 0x63, 0x55, 0x14,
            0xce, 0xd5, 0x65, 0xfe,
        ];

        assert_eq!(mac, expected);
    }

    /// RFC 4231 Test Case 4 (key with incrementing bytes)
    #[test]
    fn test_hmac_sha256_rfc4231_case4() {
        let key: [u8; 25] = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
            0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
        ];
        let data = [0xcdu8; 50];

        let mac = HmacSha256::mac(&key, &data);
        let expected: [u8; 32] = [
            0x82, 0x55, 0x8a, 0x38, 0x9a, 0x44, 0x3c, 0x0e, 0xa4, 0xcc, 0x81, 0x98, 0x99, 0xf2,
            0x08, 0x3a, 0x85, 0xf0, 0xfa, 0xa3, 0xe5, 0x78, 0xf8, 0x07, 0x7a, 0x2e, 0x3f, 0xf4,
            0x67, 0x29, 0x66, 0x5b,
        ];

        assert_eq!(mac, expected);
    }

    /// RFC 4231 Test Case 6 (131-byte key, longer than block size)
    #[test]
    fn test_hmac_sha256_rfc4231_case6() {
        let key = [0xaau8; 131];
        let data = b"Test Using Larger Than Block-Size Key - Hash Key First";

        let mac = HmacSha256::mac(&key, data);
        let expected: [u8; 32] = [
            0x60, 0xe4, 0x31, 0x59, 0x1e, 0xe0, 0xb6, 0x7f, 0x0d, 0x8a, 0x26, 0xaa, 0xcb, 0xf5,
            0xb7, 0x7f, 0x8e, 0x0b, 0xc6, 0x21, 0x37, 0x28, 0xc5, 0x14, 0x05, 0x46, 0x04, 0x0f,
            0x0e, 0xe3, 0x7f, 0x54,
        ];

        assert_eq!(mac, expected);
    }

    /// RFC 4231 Test Case 7 (131-byte key and data)
    #[test]
    fn test_hmac_sha256_rfc4231_case7() {
        let key = [0xaau8; 131];
        let data = b"This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.";

        let mac = HmacSha256::mac(&key, data);
        let expected: [u8; 32] = [
            0x9b, 0x09, 0xff, 0xa7, 0x1b, 0x94, 0x2f, 0xcb, 0x27, 0x63, 0x5f, 0xbc, 0xd5, 0xb0,
            0xe9, 0x44, 0xbf, 0xdc, 0x63, 0x64, 0x4f, 0x07, 0x13, 0x93, 0x8a, 0x7f, 0x51, 0x53,
            0x5c, 0x3a, 0x35, 0xe2,
        ];

        assert_eq!(mac, expected);
    }

    /// Test MAC verification
    #[test]
    fn test_hmac_sha256_verify() {
        let key = b"secret key";
        let data = b"message to authenticate";

        let mac = HmacSha256::mac(key, data);

        assert!(HmacSha256::verify(key, data, &mac));

        // Verify with wrong data fails
        assert!(!HmacSha256::verify(key, b"wrong message", &mac));

        // Verify with wrong key fails
        assert!(!HmacSha256::verify(b"wrong key", data, &mac));

        // Verify with wrong length fails
        assert!(!HmacSha256::verify(key, data, &mac[..31]));
    }

    /// Test incremental MAC computation
    #[test]
    fn test_hmac_sha256_incremental() {
        let key = b"test key";
        let data = b"The quick brown fox jumps over the lazy dog";

        let one_shot = HmacSha256::mac(key, data);

        let mut hmac = HmacSha256::new(key);
        hmac.update(&data[..10]);
        hmac.update(&data[10..20]);
        hmac.update(&data[20..]);
        let incremental = hmac.finalize();

        assert_eq!(one_shot, incremental);
    }

    /// Test empty message
    #[test]
    fn test_hmac_sha256_empty() {
        let key = b"key";
        let mac = HmacSha256::mac(key, b"");

        // Just verify it produces 32 bytes without panicking
        assert_eq!(mac.len(), 32);
    }

    /// Test empty key
    #[test]
    fn test_hmac_sha256_empty_key() {
        let mac = HmacSha256::mac(b"", b"message");

        // Just verify it produces 32 bytes without panicking
        assert_eq!(mac.len(), 32);
    }
}
