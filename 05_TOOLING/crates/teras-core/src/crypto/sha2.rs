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
}
