// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! SHA-256 Hash Function Implementation
//!
//! This module implements SHA-256 as specified in FIPS 180-4.
//!
//! # Constant-Time Guarantees (Law 3)
//!
//! SHA-256 is inherently constant-time for a given message length.
//! All operations are data-independent.
//!
//! # Security Notes
//!
//! - Internal state is zeroized on drop (Law 4)
//! - No memory allocation during hashing
//! - Follows FIPS 180-4 exactly

use crate::zeroize::Zeroize;

/// SHA-256 block size in bytes
pub const BLOCK_SIZE: usize = 64;
/// SHA-256 output size in bytes
pub const OUTPUT_SIZE: usize = 32;

/// Initial hash values (first 32 bits of fractional parts of square roots of first 8 primes)
const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Round constants (first 32 bits of fractional parts of cube roots of first 64 primes)
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// SHA-256 hasher state
pub struct Sha256 {
    /// Current hash state
    state: [u32; 8],
    /// Buffer for incomplete block
    buffer: [u8; BLOCK_SIZE],
    /// Number of bytes in buffer
    buffer_len: usize,
    /// Total message length in bytes (for padding)
    total_len: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256 {
    /// Create a new SHA-256 hasher
    #[must_use]
    pub fn new() -> Self {
        Self {
            state: H0,
            buffer: [0u8; BLOCK_SIZE],
            buffer_len: 0,
            total_len: 0,
        }
    }

    /// Update the hash with additional data
    pub fn update(&mut self, data: &[u8]) {
        let mut offset = 0;
        self.total_len = self.total_len.wrapping_add(data.len() as u64);

        // If we have buffered data, try to complete a block
        if self.buffer_len > 0 {
            let needed = BLOCK_SIZE - self.buffer_len;
            let available = data.len().min(needed);
            self.buffer[self.buffer_len..self.buffer_len + available]
                .copy_from_slice(&data[..available]);
            self.buffer_len += available;
            offset += available;

            if self.buffer_len == BLOCK_SIZE {
                self.compress_block(&self.buffer.clone());
                self.buffer_len = 0;
            }
        }

        // Process complete blocks directly
        while offset + BLOCK_SIZE <= data.len() {
            let block: [u8; BLOCK_SIZE] = data[offset..offset + BLOCK_SIZE]
                .try_into()
                .expect("slice is exactly BLOCK_SIZE");
            self.compress_block(&block);
            offset += BLOCK_SIZE;
        }

        // Buffer remaining data
        if offset < data.len() {
            let remaining = data.len() - offset;
            self.buffer[..remaining].copy_from_slice(&data[offset..]);
            self.buffer_len = remaining;
        }
    }

    /// Finalize the hash and return the digest
    #[must_use]
    pub fn finalize(mut self) -> [u8; OUTPUT_SIZE] {
        // Pad the message
        let bit_len = self.total_len.wrapping_mul(8);

        // Append '1' bit
        self.buffer[self.buffer_len] = 0x80;
        self.buffer_len += 1;

        // If not enough room for length, process this block and start a new one
        if self.buffer_len > BLOCK_SIZE - 8 {
            self.buffer[self.buffer_len..].fill(0);
            self.compress_block(&self.buffer.clone());
            self.buffer_len = 0;
            self.buffer.fill(0);
        } else {
            self.buffer[self.buffer_len..BLOCK_SIZE - 8].fill(0);
        }

        // Append length in bits as big-endian 64-bit integer
        self.buffer[BLOCK_SIZE - 8..].copy_from_slice(&bit_len.to_be_bytes());
        self.compress_block(&self.buffer.clone());

        // Convert state to output
        let mut output = [0u8; OUTPUT_SIZE];
        for (i, &word) in self.state.iter().enumerate() {
            output[i * 4..(i + 1) * 4].copy_from_slice(&word.to_be_bytes());
        }

        output
    }

    /// Hash data in one call
    #[must_use]
    pub fn hash(data: &[u8]) -> [u8; OUTPUT_SIZE] {
        let mut hasher = Self::new();
        hasher.update(data);
        hasher.finalize()
    }

    /// Compress a single 64-byte block
    fn compress_block(&mut self, block: &[u8; BLOCK_SIZE]) {
        // Prepare message schedule
        let mut w = [0u32; 64];

        // First 16 words are the block
        for (i, chunk) in block.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes(chunk.try_into().expect("chunk is 4 bytes"));
        }

        // Extend to 64 words
        for i in 16..64 {
            let s0 = sigma0(w[i - 15]);
            let s1 = sigma1(w[i - 2]);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        // Initialize working variables
        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];

        // Main loop
        for i in 0..64 {
            let big_s1 = big_sigma1(e);
            let ch = ch(e, f, g);
            let temp1 = h
                .wrapping_add(big_s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);

            let big_s0 = big_sigma0(a);
            let maj = maj(a, b, c);
            let temp2 = big_s0.wrapping_add(maj);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        // Update state
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);

        // Zeroize working variables
        w.zeroize();
    }
}

impl Drop for Sha256 {
    fn drop(&mut self) {
        // Zeroize internal state (Law 4)
        self.state.zeroize();
        self.buffer.zeroize();
    }
}

/// Ch function: (x AND y) XOR (NOT x AND z)
#[inline]
fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}

/// Maj function: (x AND y) XOR (x AND z) XOR (y AND z)
#[inline]
fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// Big Sigma 0 function
#[inline]
fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

/// Big Sigma 1 function
#[inline]
fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

/// Small sigma 0 function (for message schedule)
#[inline]
fn sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

/// Small sigma 1 function (for message schedule)
#[inline]
fn sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

// =============================================================================
// SHA-512 Implementation (FIPS 180-4)
// =============================================================================

/// SHA-512 block size in bytes (1024 bits)
pub const SHA512_BLOCK_SIZE: usize = 128;
/// SHA-512 output size in bytes (512 bits)
pub const SHA512_OUTPUT_SIZE: usize = 64;

/// SHA-512 initial hash values (first 64 bits of fractional parts of square roots of first 8 primes)
const SHA512_H0: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

/// SHA-512 round constants (first 64 bits of fractional parts of cube roots of first 80 primes)
const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

/// SHA-512 hasher state
pub struct Sha512 {
    /// Current hash state (8 x 64-bit words)
    state: [u64; 8],
    /// Buffer for incomplete block (128 bytes)
    buffer: [u8; SHA512_BLOCK_SIZE],
    /// Number of bytes in buffer
    buffer_len: usize,
    /// Total message length in bytes (for padding)
    /// Note: SHA-512 uses 128-bit length, but for practical purposes we use u128
    total_len: u128,
}

impl Default for Sha512 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha512 {
    /// Create a new SHA-512 hasher
    #[must_use]
    pub fn new() -> Self {
        Self {
            state: SHA512_H0,
            buffer: [0u8; SHA512_BLOCK_SIZE],
            buffer_len: 0,
            total_len: 0,
        }
    }

    /// Update the hash with additional data
    pub fn update(&mut self, data: &[u8]) {
        let mut offset = 0;
        self.total_len = self.total_len.wrapping_add(data.len() as u128);

        // If we have buffered data, try to complete a block
        if self.buffer_len > 0 {
            let needed = SHA512_BLOCK_SIZE - self.buffer_len;
            let available = data.len().min(needed);
            self.buffer[self.buffer_len..self.buffer_len + available]
                .copy_from_slice(&data[..available]);
            self.buffer_len += available;
            offset += available;

            if self.buffer_len == SHA512_BLOCK_SIZE {
                self.compress_block(&self.buffer.clone());
                self.buffer_len = 0;
            }
        }

        // Process complete blocks directly
        while offset + SHA512_BLOCK_SIZE <= data.len() {
            let block: [u8; SHA512_BLOCK_SIZE] = data[offset..offset + SHA512_BLOCK_SIZE]
                .try_into()
                .expect("slice is exactly SHA512_BLOCK_SIZE");
            self.compress_block(&block);
            offset += SHA512_BLOCK_SIZE;
        }

        // Buffer remaining data
        if offset < data.len() {
            let remaining = data.len() - offset;
            self.buffer[..remaining].copy_from_slice(&data[offset..]);
            self.buffer_len = remaining;
        }
    }

    /// Finalize the hash and return the 64-byte digest
    #[must_use]
    pub fn finalize(mut self) -> [u8; SHA512_OUTPUT_SIZE] {
        // Pad the message
        let bit_len = self.total_len.wrapping_mul(8);

        // Append '1' bit
        self.buffer[self.buffer_len] = 0x80;
        self.buffer_len += 1;

        // If not enough room for length (16 bytes), process this block and start a new one
        if self.buffer_len > SHA512_BLOCK_SIZE - 16 {
            self.buffer[self.buffer_len..].fill(0);
            self.compress_block(&self.buffer.clone());
            self.buffer_len = 0;
            self.buffer.fill(0);
        } else {
            self.buffer[self.buffer_len..SHA512_BLOCK_SIZE - 16].fill(0);
        }

        // Append length in bits as big-endian 128-bit integer
        self.buffer[SHA512_BLOCK_SIZE - 16..].copy_from_slice(&bit_len.to_be_bytes());
        self.compress_block(&self.buffer.clone());

        // Convert state to output
        let mut output = [0u8; SHA512_OUTPUT_SIZE];
        for (i, &word) in self.state.iter().enumerate() {
            output[i * 8..(i + 1) * 8].copy_from_slice(&word.to_be_bytes());
        }

        output
    }

    /// Hash data in one call
    #[must_use]
    pub fn hash(data: &[u8]) -> [u8; SHA512_OUTPUT_SIZE] {
        let mut hasher = Self::new();
        hasher.update(data);
        hasher.finalize()
    }

    /// Compress a single 128-byte block
    fn compress_block(&mut self, block: &[u8; SHA512_BLOCK_SIZE]) {
        // Prepare message schedule (80 64-bit words)
        let mut w = [0u64; 80];

        // First 16 words are the block
        for (i, chunk) in block.chunks_exact(8).enumerate() {
            w[i] = u64::from_be_bytes(chunk.try_into().expect("chunk is 8 bytes"));
        }

        // Extend to 80 words
        for i in 16..80 {
            let s0 = sha512_sigma0(w[i - 15]);
            let s1 = sha512_sigma1(w[i - 2]);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        // Initialize working variables
        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];

        // Main loop (80 rounds)
        for i in 0..80 {
            let big_s1 = sha512_big_sigma1(e);
            let ch = sha512_ch(e, f, g);
            let temp1 = h
                .wrapping_add(big_s1)
                .wrapping_add(ch)
                .wrapping_add(SHA512_K[i])
                .wrapping_add(w[i]);

            let big_s0 = sha512_big_sigma0(a);
            let maj = sha512_maj(a, b, c);
            let temp2 = big_s0.wrapping_add(maj);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        // Update state
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);

        // Zeroize working variables
        w.zeroize();
    }
}

impl Drop for Sha512 {
    fn drop(&mut self) {
        // Zeroize internal state (Law 4)
        self.state.zeroize();
        self.buffer.zeroize();
    }
}

/// SHA-512 Ch function: (x AND y) XOR (NOT x AND z)
#[inline]
fn sha512_ch(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (!x & z)
}

/// SHA-512 Maj function: (x AND y) XOR (x AND z) XOR (y AND z)
#[inline]
fn sha512_maj(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// SHA-512 Big Sigma 0 function: ROTR(28, x) XOR ROTR(34, x) XOR ROTR(39, x)
#[inline]
fn sha512_big_sigma0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}

/// SHA-512 Big Sigma 1 function: ROTR(14, x) XOR ROTR(18, x) XOR ROTR(41, x)
#[inline]
fn sha512_big_sigma1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}

/// SHA-512 Small sigma 0 function: ROTR(1, x) XOR ROTR(8, x) XOR SHR(7, x)
#[inline]
fn sha512_sigma0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}

/// SHA-512 Small sigma 1 function: ROTR(19, x) XOR ROTR(61, x) XOR SHR(6, x)
#[inline]
fn sha512_sigma1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FIPS 180-4 test vector: empty string
    #[test]
    fn test_sha256_empty() {
        let hash = Sha256::hash(b"");
        let expected: [u8; 32] = [
            0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
            0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
            0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
            0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55,
        ];
        assert_eq!(hash, expected);
    }

    /// FIPS 180-4 test vector: "abc"
    #[test]
    fn test_sha256_abc() {
        let hash = Sha256::hash(b"abc");
        let expected: [u8; 32] = [
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
            0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
            0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
            0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
        ];
        assert_eq!(hash, expected);
    }

    /// FIPS 180-4 test vector: 448 bits (one block minus padding overhead)
    #[test]
    fn test_sha256_448_bits() {
        let hash = Sha256::hash(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq");
        let expected: [u8; 32] = [
            0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
            0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
            0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
            0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1,
        ];
        assert_eq!(hash, expected);
    }

    /// FIPS 180-4 test vector: 896 bits (two blocks)
    #[test]
    fn test_sha256_896_bits() {
        let hash = Sha256::hash(
            b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
        );
        let expected: [u8; 32] = [
            0xcf, 0x5b, 0x16, 0xa7, 0x78, 0xaf, 0x83, 0x80,
            0x03, 0x6c, 0xe5, 0x9e, 0x7b, 0x04, 0x92, 0x37,
            0x0b, 0x24, 0x9b, 0x11, 0xe8, 0xf0, 0x7a, 0x51,
            0xaf, 0xac, 0x45, 0x03, 0x7a, 0xfe, 0xe9, 0xd1,
        ];
        assert_eq!(hash, expected);
    }

    /// Test incremental hashing produces same result as one-shot
    #[test]
    fn test_sha256_incremental() {
        let data = b"The quick brown fox jumps over the lazy dog";
        
        let one_shot = Sha256::hash(data);
        
        let mut hasher = Sha256::new();
        hasher.update(&data[..10]);
        hasher.update(&data[10..20]);
        hasher.update(&data[20..]);
        let incremental = hasher.finalize();
        
        assert_eq!(one_shot, incremental);
    }

    /// Test byte-by-byte update
    #[test]
    fn test_sha256_byte_by_byte() {
        let data = b"Hello, World!";
        
        let one_shot = Sha256::hash(data);
        
        let mut hasher = Sha256::new();
        for &byte in data.iter() {
            hasher.update(&[byte]);
        }
        let byte_by_byte = hasher.finalize();
        
        assert_eq!(one_shot, byte_by_byte);
    }

    /// Test with exactly one block
    #[test]
    fn test_sha256_one_block() {
        // 55 bytes + 1 byte (0x80) + 8 bytes length = 64 bytes (one block)
        let data = &[0x41u8; 55]; // 55 'A's
        let hash = Sha256::hash(data);
        
        // Just verify it runs without panic and produces 32 bytes
        assert_eq!(hash.len(), 32);
    }

    /// Test with data that requires exactly two blocks
    #[test]
    fn test_sha256_two_blocks() {
        // 56 bytes requires two blocks (56 + 1 + 8 > 64)
        let data = &[0x42u8; 56]; // 56 'B's
        let hash = Sha256::hash(data);
        
        assert_eq!(hash.len(), 32);
    }

    /// Test large input (multiple blocks)
    #[test]
    fn test_sha256_large_input() {
        let data = &[0x43u8; 1000]; // 1000 bytes
        let hash = Sha256::hash(data);

        assert_eq!(hash.len(), 32);
    }

    // =========================================================================
    // SHA-512 Tests (FIPS 180-4)
    // =========================================================================

    /// FIPS 180-4 test vector: SHA-512 empty string
    #[test]
    fn test_sha512_empty() {
        let hash = Sha512::hash(b"");
        let expected: [u8; 64] = [
            0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd,
            0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d, 0x80, 0x07,
            0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc,
            0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce,
            0x47, 0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0,
            0xff, 0x83, 0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f,
            0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a, 0x81,
            0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e,
        ];
        assert_eq!(hash, expected);
    }

    /// FIPS 180-4 test vector: SHA-512 "abc"
    #[test]
    fn test_sha512_abc() {
        let hash = Sha512::hash(b"abc");
        let expected: [u8; 64] = [
            0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
            0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
            0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
            0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
            0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
            0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
            0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
            0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
        ];
        assert_eq!(hash, expected);
    }

    /// FIPS 180-4 test vector: SHA-512 two-block message
    #[test]
    fn test_sha512_896_bits() {
        let hash = Sha512::hash(
            b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
        );
        let expected: [u8; 64] = [
            0x8e, 0x95, 0x9b, 0x75, 0xda, 0xe3, 0x13, 0xda,
            0x8c, 0xf4, 0xf7, 0x28, 0x14, 0xfc, 0x14, 0x3f,
            0x8f, 0x77, 0x79, 0xc6, 0xeb, 0x9f, 0x7f, 0xa1,
            0x72, 0x99, 0xae, 0xad, 0xb6, 0x88, 0x90, 0x18,
            0x50, 0x1d, 0x28, 0x9e, 0x49, 0x00, 0xf7, 0xe4,
            0x33, 0x1b, 0x99, 0xde, 0xc4, 0xb5, 0x43, 0x3a,
            0xc7, 0xd3, 0x29, 0xee, 0xb6, 0xdd, 0x26, 0x54,
            0x5e, 0x96, 0xe5, 0x5b, 0x87, 0x4b, 0xe9, 0x09,
        ];
        assert_eq!(hash, expected);
    }

    /// Test SHA-512 incremental hashing produces same result as one-shot
    #[test]
    fn test_sha512_incremental() {
        let data = b"The quick brown fox jumps over the lazy dog";

        let one_shot = Sha512::hash(data);

        let mut hasher = Sha512::new();
        hasher.update(&data[..10]);
        hasher.update(&data[10..20]);
        hasher.update(&data[20..]);
        let incremental = hasher.finalize();

        assert_eq!(one_shot, incremental);
    }

    /// Test SHA-512 byte-by-byte update
    #[test]
    fn test_sha512_byte_by_byte() {
        let data = b"Hello, World!";

        let one_shot = Sha512::hash(data);

        let mut hasher = Sha512::new();
        for &byte in data.iter() {
            hasher.update(&[byte]);
        }
        let byte_by_byte = hasher.finalize();

        assert_eq!(one_shot, byte_by_byte);
    }

    /// Test SHA-512 with one block
    #[test]
    fn test_sha512_one_block() {
        // 111 bytes + 1 byte (0x80) + 16 bytes length = 128 bytes (one block)
        let data = &[0x41u8; 111]; // 111 'A's
        let hash = Sha512::hash(data);

        assert_eq!(hash.len(), 64);
    }

    /// Test SHA-512 with two blocks
    #[test]
    fn test_sha512_two_blocks() {
        // 112 bytes requires two blocks (112 + 1 + 16 > 128)
        let data = &[0x42u8; 112]; // 112 'B's
        let hash = Sha512::hash(data);

        assert_eq!(hash.len(), 64);
    }
}
