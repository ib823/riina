// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! AES-256-GCM Authenticated Encryption Implementation
//!
//! This module implements AES-256-GCM as specified in NIST SP 800-38D.
//! GCM provides both confidentiality (via AES-CTR) and authenticity (via GHASH).
//!
//! # Law 2: Cryptographic Non-Negotiables
//!
//! - Uses AES-256 (256-bit symmetric encryption)
//! - 128-bit authentication tag
//! - 96-bit nonce (recommended)
//!
//! # Security Notes
//!
//! - NEVER reuse a nonce with the same key
//! - The 96-bit nonce allows for 2^32 messages per key safely
//! - All sensitive data is zeroized on drop (Law 4)
//! - All operations are constant-time (Law 3)

use crate::crypto::aes::{Aes256, BLOCK_SIZE, KEY_SIZE as AES_KEY_SIZE};
use crate::crypto::ghash::Ghash;
use crate::crypto::{Aead, CryptoError, CryptoResult};
use crate::zeroize::Zeroize;

/// AES-256-GCM key size (32 bytes)
pub const KEY_SIZE: usize = AES_KEY_SIZE;
/// AES-256-GCM nonce size (12 bytes, recommended)
pub const NONCE_SIZE: usize = 12;
/// AES-256-GCM tag size (16 bytes)
pub const TAG_SIZE: usize = 16;

/// AES-256-GCM cipher
pub struct Aes256Gcm {
    /// AES-256 cipher for encryption
    cipher: Aes256,
    /// Hash key H = AES_K(0^128)
    h: [u8; BLOCK_SIZE],
}

impl Aes256Gcm {
    /// Create a new AES-256-GCM instance from a 32-byte key
    ///
    /// # Panics
    /// Panics if key is not exactly 32 bytes.
    #[must_use]
    pub fn new(key: &[u8; KEY_SIZE]) -> Self {
        let cipher = Aes256::new(key);
        
        // Compute H = AES_K(0^128)
        let mut h = [0u8; BLOCK_SIZE];
        cipher.encrypt_block(&mut h);
        
        Self { cipher, h }
    }

    /// Encrypt plaintext and produce ciphertext with authentication tag
    ///
    /// # Arguments
    /// * `nonce` - 12-byte nonce (MUST be unique for each message)
    /// * `aad` - Additional authenticated data (not encrypted, but authenticated)
    /// * `plaintext` - Data to encrypt
    /// * `output` - Buffer for ciphertext + tag (must be `plaintext.len() + 16` bytes)
    ///
    /// # Returns
    /// The number of bytes written to output (plaintext.len() + 16)
    ///
    /// # Errors
    /// - `InvalidNonceLength` if nonce is not 12 bytes
    /// - `BufferTooSmall` if output is too small
    pub fn encrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
        output: &mut [u8],
    ) -> CryptoResult<usize> {
        if nonce.len() != NONCE_SIZE {
            return Err(CryptoError::InvalidNonceLength);
        }
        if output.len() < plaintext.len() + TAG_SIZE {
            return Err(CryptoError::BufferTooSmall);
        }

        // Compute initial counter J0
        let j0 = compute_j0(nonce);

        // Encrypt plaintext using GCTR with J0 incremented by 1
        let mut counter = j0;
        inc32(&mut counter);
        gctr(&self.cipher, &counter, plaintext, &mut output[..plaintext.len()]);

        // Compute authentication tag
        let ciphertext = &output[..plaintext.len()];
        let tag = self.compute_tag(aad, ciphertext, &j0);
        output[plaintext.len()..plaintext.len() + TAG_SIZE].copy_from_slice(&tag);

        Ok(plaintext.len() + TAG_SIZE)
    }

    /// Decrypt ciphertext and verify authentication tag
    ///
    /// # Arguments
    /// * `nonce` - 12-byte nonce (same as used for encryption)
    /// * `aad` - Additional authenticated data (same as used for encryption)
    /// * `ciphertext` - Ciphertext + tag (at least 16 bytes)
    /// * `output` - Buffer for plaintext (must be `ciphertext.len() - 16` bytes)
    ///
    /// # Returns
    /// The number of bytes written to output
    ///
    /// # Errors
    /// - `InvalidNonceLength` if nonce is not 12 bytes
    /// - `InvalidInputLength` if ciphertext is too short
    /// - `BufferTooSmall` if output is too small
    /// - `AuthenticationFailed` if tag verification fails
    pub fn decrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        output: &mut [u8],
    ) -> CryptoResult<usize> {
        if nonce.len() != NONCE_SIZE {
            return Err(CryptoError::InvalidNonceLength);
        }
        if ciphertext.len() < TAG_SIZE {
            return Err(CryptoError::InvalidInputLength);
        }

        let ct_len = ciphertext.len() - TAG_SIZE;
        if output.len() < ct_len {
            return Err(CryptoError::BufferTooSmall);
        }

        let ct = &ciphertext[..ct_len];
        let tag = &ciphertext[ct_len..];

        // Compute initial counter J0
        let j0 = compute_j0(nonce);

        // Compute expected tag
        let expected_tag = self.compute_tag(aad, ct, &j0);

        // Verify tag in constant time
        if !constant_time_eq(tag, &expected_tag) {
            return Err(CryptoError::AuthenticationFailed);
        }

        // Decrypt ciphertext using GCTR with J0 incremented by 1
        let mut counter = j0;
        inc32(&mut counter);
        gctr(&self.cipher, &counter, ct, output);

        Ok(ct_len)
    }

    /// Compute the GCM authentication tag
    fn compute_tag(
        &self,
        aad: &[u8],
        ciphertext: &[u8],
        j0: &[u8; BLOCK_SIZE],
    ) -> [u8; TAG_SIZE] {
        // S = GHASH_H(A || 0^s || C || 0^u || [len(A)]_64 || [len(C)]_64)
        let s = Ghash::compute(&self.h, aad, ciphertext);

        // T = MSB_t(GCTR_K(J0, S))
        let mut tag = [0u8; TAG_SIZE];
        gctr(&self.cipher, j0, &s, &mut tag);

        tag
    }

    /// Encrypt in place (ciphertext replaces plaintext, tag appended)
    ///
    /// # Arguments
    /// * `nonce` - 12-byte nonce
    /// * `aad` - Additional authenticated data
    /// * `buffer` - Buffer containing plaintext, must have room for tag
    /// * `plaintext_len` - Length of plaintext in buffer
    ///
    /// # Returns
    /// The total length (plaintext_len + 16)
    ///
    /// # Errors
    /// Same as `encrypt`
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        buffer: &mut [u8],
        plaintext_len: usize,
    ) -> CryptoResult<usize> {
        if nonce.len() != NONCE_SIZE {
            return Err(CryptoError::InvalidNonceLength);
        }
        if buffer.len() < plaintext_len + TAG_SIZE {
            return Err(CryptoError::BufferTooSmall);
        }

        let j0 = compute_j0(nonce);
        let mut counter = j0;
        inc32(&mut counter);

        // Encrypt in place
        gctr_in_place(&self.cipher, &counter, &mut buffer[..plaintext_len]);

        // Compute and append tag
        let tag = self.compute_tag(aad, &buffer[..plaintext_len], &j0);
        buffer[plaintext_len..plaintext_len + TAG_SIZE].copy_from_slice(&tag);

        Ok(plaintext_len + TAG_SIZE)
    }

    /// Decrypt in place (plaintext replaces ciphertext)
    ///
    /// # Arguments
    /// * `nonce` - 12-byte nonce
    /// * `aad` - Additional authenticated data
    /// * `buffer` - Buffer containing ciphertext + tag
    ///
    /// # Returns
    /// The plaintext length (buffer.len() - 16)
    ///
    /// # Errors
    /// Same as `decrypt`
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        buffer: &mut [u8],
    ) -> CryptoResult<usize> {
        if nonce.len() != NONCE_SIZE {
            return Err(CryptoError::InvalidNonceLength);
        }
        if buffer.len() < TAG_SIZE {
            return Err(CryptoError::InvalidInputLength);
        }

        let ct_len = buffer.len() - TAG_SIZE;
        let j0 = compute_j0(nonce);

        // Verify tag first
        let expected_tag = self.compute_tag(aad, &buffer[..ct_len], &j0);
        if !constant_time_eq(&buffer[ct_len..], &expected_tag) {
            return Err(CryptoError::AuthenticationFailed);
        }

        // Decrypt in place
        let mut counter = j0;
        inc32(&mut counter);
        gctr_in_place(&self.cipher, &counter, &mut buffer[..ct_len]);

        Ok(ct_len)
    }
}

impl Aead for Aes256Gcm {
    const KEY_SIZE: usize = KEY_SIZE;
    const NONCE_SIZE: usize = NONCE_SIZE;
    const TAG_SIZE: usize = TAG_SIZE;

    fn new(key: &[u8]) -> CryptoResult<Self> {
        if key.len() != KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        let key_array: [u8; KEY_SIZE] = key.try_into().expect("length checked");
        Ok(Self::new(&key_array))
    }

    fn encrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
        output: &mut [u8],
    ) -> CryptoResult<usize> {
        self.encrypt(nonce, aad, plaintext, output)
    }

    fn decrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        output: &mut [u8],
    ) -> CryptoResult<usize> {
        self.decrypt(nonce, aad, ciphertext, output)
    }
}

impl Drop for Aes256Gcm {
    fn drop(&mut self) {
        // Zeroize hash key (Law 4)
        self.h.zeroize();
    }
}

/// Compute J0 from nonce (for 96-bit nonce)
fn compute_j0(nonce: &[u8]) -> [u8; BLOCK_SIZE] {
    let mut j0 = [0u8; BLOCK_SIZE];
    j0[..NONCE_SIZE].copy_from_slice(nonce);
    j0[BLOCK_SIZE - 1] = 1; // Counter starts at 1
    j0
}

/// Increment the rightmost 32 bits of a 128-bit counter
fn inc32(counter: &mut [u8; BLOCK_SIZE]) {
    let mut carry = 1u16;
    for i in (BLOCK_SIZE - 4..BLOCK_SIZE).rev() {
        let sum = u16::from(counter[i]) + carry;
        counter[i] = sum as u8;
        carry = sum >> 8;
    }
}

/// GCTR function: CTR mode encryption/decryption
fn gctr(cipher: &Aes256, icb: &[u8; BLOCK_SIZE], input: &[u8], output: &mut [u8]) {
    let mut counter = *icb;
    let mut offset = 0;

    while offset < input.len() {
        // Encrypt counter block
        let mut keystream = counter;
        cipher.encrypt_block(&mut keystream);

        // XOR with input
        let remaining = input.len() - offset;
        let block_len = remaining.min(BLOCK_SIZE);

        for i in 0..block_len {
            output[offset + i] = input[offset + i] ^ keystream[i];
        }

        offset += block_len;
        inc32(&mut counter);
    }
}

/// GCTR in place
fn gctr_in_place(cipher: &Aes256, icb: &[u8; BLOCK_SIZE], data: &mut [u8]) {
    let mut counter = *icb;
    let mut offset = 0;

    while offset < data.len() {
        let mut keystream = counter;
        cipher.encrypt_block(&mut keystream);

        let remaining = data.len() - offset;
        let block_len = remaining.min(BLOCK_SIZE);

        for i in 0..block_len {
            data[offset + i] ^= keystream[i];
        }

        offset += block_len;
        inc32(&mut counter);
    }
}

/// Constant-time comparison
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    
    diff == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// NIST GCM Test Vector - Case 1 (empty plaintext and AAD)
    #[test]
    fn test_aes256_gcm_case1() {
        let key: [u8; 32] = [0u8; 32];
        let nonce: [u8; 12] = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext: &[u8] = &[];
        
        let cipher = Aes256Gcm::new(&key);
        let mut ciphertext = [0u8; 16]; // Just the tag
        
        let len = cipher.encrypt(&nonce, aad, plaintext, &mut ciphertext).unwrap();
        assert_eq!(len, 16);
        
        // Verify decryption
        let mut decrypted = [0u8; 0];
        let dec_len = cipher.decrypt(&nonce, aad, &ciphertext, &mut decrypted).unwrap();
        assert_eq!(dec_len, 0);
    }

    /// NIST GCM Test Vector - Case 2 (empty AAD, 16-byte plaintext)
    #[test]
    fn test_aes256_gcm_case2() {
        let key: [u8; 32] = [0u8; 32];
        let nonce: [u8; 12] = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext: [u8; 16] = [0u8; 16];
        
        let cipher = Aes256Gcm::new(&key);
        let mut ciphertext = [0u8; 32]; // 16 CT + 16 tag
        
        let len = cipher.encrypt(&nonce, aad, &plaintext, &mut ciphertext).unwrap();
        assert_eq!(len, 32);
        
        // Verify decryption
        let mut decrypted = [0u8; 16];
        let dec_len = cipher.decrypt(&nonce, aad, &ciphertext[..32], &mut decrypted).unwrap();
        assert_eq!(dec_len, 16);
        assert_eq!(decrypted, plaintext);
    }

    /// Test with AAD
    #[test]
    fn test_aes256_gcm_with_aad() {
        let key: [u8; 32] = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
            0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
            0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
            0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
        ];
        let nonce: [u8; 12] = [0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce, 0xdb, 0xad, 0xde, 0xca, 0xf8, 0x88];
        let aad = b"Additional Authenticated Data";
        let plaintext = b"Plaintext message to encrypt";
        
        let cipher = Aes256Gcm::new(&key);
        let mut ciphertext = vec![0u8; plaintext.len() + 16];
        
        let len = cipher.encrypt(&nonce, aad, plaintext, &mut ciphertext).unwrap();
        assert_eq!(len, plaintext.len() + 16);
        
        // Verify decryption
        let mut decrypted = vec![0u8; plaintext.len()];
        let dec_len = cipher.decrypt(&nonce, aad, &ciphertext, &mut decrypted).unwrap();
        assert_eq!(dec_len, plaintext.len());
        assert_eq!(decrypted.as_slice(), plaintext);
    }

    /// Test authentication failure with wrong AAD
    #[test]
    fn test_aes256_gcm_auth_failure_aad() {
        let key: [u8; 32] = [0x42; 32];
        let nonce: [u8; 12] = [0x24; 12];
        let aad = b"correct AAD";
        let plaintext = b"secret message";
        
        let cipher = Aes256Gcm::new(&key);
        let mut ciphertext = vec![0u8; plaintext.len() + 16];
        cipher.encrypt(&nonce, aad, plaintext, &mut ciphertext).unwrap();
        
        // Decrypt with wrong AAD
        let mut decrypted = vec![0u8; plaintext.len()];
        let result = cipher.decrypt(&nonce, b"wrong AAD", &ciphertext, &mut decrypted);
        assert!(matches!(result, Err(CryptoError::AuthenticationFailed)));
    }

    /// Test authentication failure with modified ciphertext
    #[test]
    fn test_aes256_gcm_auth_failure_ct() {
        let key: [u8; 32] = [0x42; 32];
        let nonce: [u8; 12] = [0x24; 12];
        let aad = b"AAD";
        let plaintext = b"secret message";
        
        let cipher = Aes256Gcm::new(&key);
        let mut ciphertext = vec![0u8; plaintext.len() + 16];
        cipher.encrypt(&nonce, aad, plaintext, &mut ciphertext).unwrap();
        
        // Modify ciphertext
        ciphertext[0] ^= 0xff;
        
        let mut decrypted = vec![0u8; plaintext.len()];
        let result = cipher.decrypt(&nonce, aad, &ciphertext, &mut decrypted);
        assert!(matches!(result, Err(CryptoError::AuthenticationFailed)));
    }

    /// Test in-place encryption/decryption
    #[test]
    fn test_aes256_gcm_in_place() {
        let key: [u8; 32] = [0xde; 32];
        let nonce: [u8; 12] = [0xad; 12];
        let aad = b"header";
        let plaintext = b"message to encrypt in place";
        
        let cipher = Aes256Gcm::new(&key);
        
        // Encrypt in place
        let mut buffer = vec![0u8; plaintext.len() + 16];
        buffer[..plaintext.len()].copy_from_slice(plaintext);
        let len = cipher.encrypt_in_place(&nonce, aad, &mut buffer, plaintext.len()).unwrap();
        assert_eq!(len, plaintext.len() + 16);
        
        // Decrypt in place
        let dec_len = cipher.decrypt_in_place(&nonce, aad, &mut buffer).unwrap();
        assert_eq!(dec_len, plaintext.len());
        assert_eq!(&buffer[..dec_len], plaintext);
    }

    /// Test invalid nonce length
    #[test]
    fn test_aes256_gcm_invalid_nonce() {
        let key: [u8; 32] = [0u8; 32];
        let cipher = Aes256Gcm::new(&key);
        
        let mut output = [0u8; 32];
        
        // Too short
        let result = cipher.encrypt(&[0u8; 8], &[], &[0u8; 16], &mut output);
        assert!(matches!(result, Err(CryptoError::InvalidNonceLength)));
        
        // Too long
        let result = cipher.encrypt(&[0u8; 16], &[], &[0u8; 16], &mut output);
        assert!(matches!(result, Err(CryptoError::InvalidNonceLength)));
    }

    /// Test counter increment
    #[test]
    fn test_inc32() {
        let mut counter: [u8; 16] = [0; 16];
        counter[15] = 0xff;
        counter[14] = 0xff;
        counter[13] = 0xff;
        counter[12] = 0xff;
        
        inc32(&mut counter);
        
        // Should wrap to 0
        assert_eq!(counter[12..16], [0, 0, 0, 0]);
    }

    /// Test large message
    #[test]
    fn test_aes256_gcm_large_message() {
        let key: [u8; 32] = [0xab; 32];
        let nonce: [u8; 12] = [0xcd; 12];
        let aad = b"large message test";
        let plaintext = vec![0x42u8; 1024 * 10]; // 10 KB
        
        let cipher = Aes256Gcm::new(&key);
        let mut ciphertext = vec![0u8; plaintext.len() + 16];
        
        let len = cipher.encrypt(&nonce, aad, &plaintext, &mut ciphertext).unwrap();
        assert_eq!(len, plaintext.len() + 16);
        
        let mut decrypted = vec![0u8; plaintext.len()];
        let dec_len = cipher.decrypt(&nonce, aad, &ciphertext, &mut decrypted).unwrap();
        assert_eq!(dec_len, plaintext.len());
        assert_eq!(decrypted, plaintext);
    }
}
