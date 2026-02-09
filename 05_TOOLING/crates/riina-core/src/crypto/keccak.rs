// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Keccak and SHAKE Implementation (FIPS 202)
//!
//! This module implements the Keccak-f[1600] permutation and the SHAKE128/SHAKE256
//! extendable-output functions (XOFs) as specified in FIPS 202.
//!
//! # FIPS 202 Compliance
//!
//! This implementation follows FIPS 202 "SHA-3 Standard: Permutation-Based Hash and
//! Extendable-Output Functions" exactly. Every constant, rotation amount, and
//! algorithmic step is derived directly from the specification.
//!
//! # Security Properties
//!
//! - SHAKE128: 128-bit security level (256-bit capacity)
//! - SHAKE256: 256-bit security level (512-bit capacity)
//! - Collision resistance: min(d/2, c/2) bits where d is output length, c is capacity
//! - Preimage resistance: min(d, c/2) bits
//!
//! # Implementation Notes
//!
//! - State is represented as 25 64-bit lanes (5×5×64 = 1600 bits)
//! - All operations are designed to be constant-time
//! - No table lookups indexed by secret data
//! - Zeroization of sensitive state on drop (Law 4)
//!
//! # References
//!
//! - FIPS 202: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
//! - Keccak Reference: https://keccak.team/keccak_specs_summary.html

use crate::zeroize::Zeroize;

// =============================================================================
// Keccak-f[1600] Constants (FIPS 202, Section 3.2)
// =============================================================================

/// Number of rounds for Keccak-f[1600]
/// nr = 12 + 2*l where l = log2(64) = 6, so nr = 12 + 12 = 24
const KECCAK_ROUNDS: usize = 24;

/// Round constants for the ι (iota) step
/// RC[i] for i = 0..23, computed as per FIPS 202 Algorithm 5
/// Each constant is a 64-bit value with bits set at positions 2^j - 1 for j = 0..6
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// Rotation offsets for the ρ (rho) step
/// r[x,y] for the lane at position (x,y), computed per FIPS 202 Section 3.2.2
/// Indexed as ROTATION_OFFSETS[x + 5*y]
const ROTATION_OFFSETS: [u32; 25] = [
    //  x=0   x=1   x=2   x=3   x=4
    0, 1, 62, 28, 27, // y=0
    36, 44, 6, 55, 20, // y=1
    3, 10, 43, 25, 39, // y=2
    41, 45, 15, 21, 8, // y=3
    18, 2, 61, 56, 14, // y=4
];

/// π (pi) step permutation indices
/// Maps position i to position π(i) where B[y, (2x+3y) mod 5] = A[x,y]
/// PI_LANE[j] gives the source lane index for destination lane j
///
/// Computed from: input (x,y) → output (y, (2x+3y) mod 5)
/// With linear indexing: input[x + 5*y] → output[y + 5*((2x+3y) mod 5)]
///
/// For each output position j, find which input position i maps to it:
/// j=0←i=0, j=1←i=6, j=2←i=12, j=3←i=18, j=4←i=24,
/// j=5←i=3, j=6←i=9, j=7←i=10, j=8←i=16, j=9←i=22,
/// j=10←i=1, j=11←i=7, j=12←i=13, j=13←i=19, j=14←i=20,
/// j=15←i=4, j=16←i=5, j=17←i=11, j=18←i=17, j=19←i=23,
/// j=20←i=2, j=21←i=8, j=22←i=14, j=23←i=15, j=24←i=21
const PI_LANE: [usize; 25] = [
    0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
];

// =============================================================================
// Keccak State
// =============================================================================

/// The Keccak state: 5×5 array of 64-bit lanes (1600 bits total)
///
/// The state is indexed as state[x + 5*y] for lane (x,y).
/// Bit j of lane (x,y) corresponds to bit (x,y,z) where z = j.
#[derive(Clone)]
pub struct KeccakState {
    /// 25 lanes of 64 bits each
    lanes: [u64; 25],
}

impl KeccakState {
    /// Create a new zero-initialized state
    #[inline]
    pub fn new() -> Self {
        Self { lanes: [0u64; 25] }
    }

    /// XOR a byte into the state at a specific byte position
    /// Position is in bytes (0..199)
    #[inline]
    pub fn xor_byte(&mut self, position: usize, byte: u8) {
        debug_assert!(position < 200);
        let lane_idx = position / 8;
        let byte_idx = position % 8;
        self.lanes[lane_idx] ^= u64::from(byte) << (8 * byte_idx);
    }

    /// XOR a block of bytes into the state (for absorbing)
    /// The block length must not exceed 200 bytes
    pub fn xor_bytes(&mut self, bytes: &[u8]) {
        debug_assert!(bytes.len() <= 200);

        // XOR full lanes (8 bytes at a time) for efficiency
        let full_lanes = bytes.len() / 8;
        for i in 0..full_lanes {
            let lane_bytes: [u8; 8] = bytes[i * 8..(i + 1) * 8].try_into().unwrap();
            self.lanes[i] ^= u64::from_le_bytes(lane_bytes);
        }

        // XOR remaining bytes
        let remaining_start = full_lanes * 8;
        for (i, &byte) in bytes[remaining_start..].iter().enumerate() {
            self.xor_byte(remaining_start + i, byte);
        }
    }

    /// Extract bytes from the state (for squeezing)
    pub fn extract_bytes(&self, output: &mut [u8]) {
        debug_assert!(output.len() <= 200);

        // Extract full lanes
        let full_lanes = output.len() / 8;
        for i in 0..full_lanes {
            output[i * 8..(i + 1) * 8].copy_from_slice(&self.lanes[i].to_le_bytes());
        }

        // Extract remaining bytes
        let remaining_start = full_lanes * 8;
        if remaining_start < output.len() {
            let last_lane_bytes = self.lanes[full_lanes].to_le_bytes();
            for (i, byte) in output[remaining_start..].iter_mut().enumerate() {
                *byte = last_lane_bytes[i];
            }
        }
    }

    /// Apply the Keccak-f[1600] permutation
    ///
    /// This is the core of Keccak, applying 24 rounds of:
    /// θ (theta) → ρ (rho) → π (pi) → χ (chi) → ι (iota)
    pub fn permute(&mut self) {
        for round in 0..KECCAK_ROUNDS {
            self.round(round);
        }
    }

    /// Apply a single round of Keccak-f[1600]
    #[inline]
    fn round(&mut self, round_idx: usize) {
        // θ (theta) step - Column parity mixing
        self.theta();

        // ρ (rho) step - Bit rotation within lanes
        self.rho();

        // π (pi) step - Lane permutation
        self.pi();

        // χ (chi) step - Non-linear mixing
        self.chi();

        // ι (iota) step - Round constant XOR
        self.iota(round_idx);
    }

    /// θ (theta) step: Column parity diffusion
    ///
    /// C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]
    /// D[x] = C[x-1] ⊕ rot(C[x+1], 1)
    /// A'[x,y] = A[x,y] ⊕ D[x]
    #[inline]
    fn theta(&mut self) {
        // Compute column parities C[x] for x = 0..4
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = self.lanes[x]
                ^ self.lanes[x + 5]
                ^ self.lanes[x + 10]
                ^ self.lanes[x + 15]
                ^ self.lanes[x + 20];
        }

        // Compute D[x] and XOR into all lanes
        for x in 0..5 {
            // D[x] = C[x-1 mod 5] ⊕ rot(C[x+1 mod 5], 1)
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);

            // XOR D[x] into all lanes in column x
            self.lanes[x] ^= d;
            self.lanes[x + 5] ^= d;
            self.lanes[x + 10] ^= d;
            self.lanes[x + 15] ^= d;
            self.lanes[x + 20] ^= d;
        }
    }

    /// ρ (rho) step: Bit rotation within lanes
    ///
    /// A'[x,y] = rot(A[x,y], r[x,y])
    /// where r[x,y] are fixed rotation offsets per FIPS 202
    #[inline]
    fn rho(&mut self) {
        for i in 0..25 {
            self.lanes[i] = self.lanes[i].rotate_left(ROTATION_OFFSETS[i]);
        }
    }

    /// π (pi) step: Lane permutation
    ///
    /// A'[y, 2x+3y mod 5] = A[x,y]
    /// Equivalently: A'[π(x,y)] = A[x,y]
    #[inline]
    fn pi(&mut self) {
        let mut temp = [0u64; 25];
        for i in 0..25 {
            temp[i] = self.lanes[PI_LANE[i]];
        }
        self.lanes = temp;
    }

    /// χ (chi) step: Non-linear row mixing
    ///
    /// A'[x,y] = A[x,y] ⊕ ((¬A[x+1,y]) ∧ A[x+2,y])
    ///
    /// This is the only non-linear step in Keccak.
    #[inline]
    fn chi(&mut self) {
        for y in 0..5 {
            let base = y * 5;

            // Load the 5 lanes in this row
            let a0 = self.lanes[base];
            let a1 = self.lanes[base + 1];
            let a2 = self.lanes[base + 2];
            let a3 = self.lanes[base + 3];
            let a4 = self.lanes[base + 4];

            // Compute χ for each lane
            self.lanes[base] = a0 ^ ((!a1) & a2);
            self.lanes[base + 1] = a1 ^ ((!a2) & a3);
            self.lanes[base + 2] = a2 ^ ((!a3) & a4);
            self.lanes[base + 3] = a3 ^ ((!a4) & a0);
            self.lanes[base + 4] = a4 ^ ((!a0) & a1);
        }
    }

    /// ι (iota) step: Round constant addition
    ///
    /// A'[0,0] = A[0,0] ⊕ RC[round]
    #[inline]
    fn iota(&mut self, round_idx: usize) {
        self.lanes[0] ^= RC[round_idx];
    }
}

impl Default for KeccakState {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for KeccakState {
    fn drop(&mut self) {
        // Zeroize the state (Law 4: All secrets must be zeroized)
        self.lanes.zeroize();
    }
}

// =============================================================================
// Keccak Sponge Construction
// =============================================================================

/// Keccak sponge with configurable rate
pub struct KeccakSponge {
    /// The Keccak state
    state: KeccakState,
    /// Rate in bytes (r/8)
    rate_bytes: usize,
    /// Current position in the rate portion (for incremental absorb/squeeze)
    position: usize,
    /// Domain separation suffix (0x1F for SHAKE, 0x06 for SHA-3)
    suffix: u8,
    /// Whether we've started squeezing (absorb phase is complete)
    squeezed: bool,
}

impl KeccakSponge {
    /// Create a new Keccak sponge
    ///
    /// # Arguments
    /// * `rate_bytes` - Rate in bytes (168 for SHAKE128, 136 for SHAKE256)
    /// * `suffix` - Domain separation suffix (0x1F for SHAKE XOF)
    pub fn new(rate_bytes: usize, suffix: u8) -> Self {
        debug_assert!(rate_bytes <= 200);
        debug_assert!(rate_bytes > 0);

        Self {
            state: KeccakState::new(),
            rate_bytes,
            position: 0,
            suffix,
            squeezed: false,
        }
    }

    /// Absorb input data into the sponge
    ///
    /// Can be called multiple times before squeezing.
    pub fn absorb(&mut self, data: &[u8]) {
        debug_assert!(!self.squeezed, "Cannot absorb after squeezing");

        let mut offset = 0;

        // If we have a partial block, try to fill it
        if self.position > 0 {
            let remaining = self.rate_bytes - self.position;
            let to_copy = core::cmp::min(remaining, data.len());

            for i in 0..to_copy {
                self.state.xor_byte(self.position + i, data[i]);
            }

            self.position += to_copy;
            offset += to_copy;

            if self.position == self.rate_bytes {
                self.state.permute();
                self.position = 0;
            }
        }

        // Process full blocks
        while offset + self.rate_bytes <= data.len() {
            self.state
                .xor_bytes(&data[offset..offset + self.rate_bytes]);
            self.state.permute();
            offset += self.rate_bytes;
        }

        // Store remaining partial block
        if offset < data.len() {
            let remaining = data.len() - offset;
            for i in 0..remaining {
                self.state.xor_byte(i, data[offset + i]);
            }
            self.position = remaining;
        }
    }

    /// Finalize the absorb phase and begin squeezing
    ///
    /// This applies the padding rule and is called automatically before
    /// the first squeeze if not called explicitly.
    fn finalize_absorb(&mut self) {
        if self.squeezed {
            return;
        }

        // Apply padding: suffix || 10*1
        // XOR the suffix byte at the current position
        self.state.xor_byte(self.position, self.suffix);

        // XOR 0x80 at the last byte of the rate
        // Note: If position == rate_bytes - 1 and suffix has high bit set,
        // this will XOR both suffix and 0x80 into the same byte position
        self.state.xor_byte(self.rate_bytes - 1, 0x80);

        // Final permutation
        self.state.permute();

        self.position = 0;
        self.squeezed = true;
    }

    /// Squeeze output data from the sponge
    ///
    /// Can be called multiple times to produce arbitrarily long output (XOF).
    pub fn squeeze(&mut self, output: &mut [u8]) {
        // Finalize absorb phase if not done
        if !self.squeezed {
            self.finalize_absorb();
        }

        let mut offset = 0;

        // If we have leftover from previous squeeze, use it
        if self.position > 0 {
            let available = self.rate_bytes - self.position;
            let to_copy = core::cmp::min(available, output.len());

            let mut temp = [0u8; 200];
            self.state.extract_bytes(&mut temp[..self.rate_bytes]);
            output[..to_copy].copy_from_slice(&temp[self.position..self.position + to_copy]);

            self.position += to_copy;
            offset += to_copy;

            if self.position == self.rate_bytes {
                self.state.permute();
                self.position = 0;
            }
        }

        // Squeeze full blocks
        while offset + self.rate_bytes <= output.len() {
            self.state
                .extract_bytes(&mut output[offset..offset + self.rate_bytes]);
            self.state.permute();
            offset += self.rate_bytes;
        }

        // Squeeze partial final block
        if offset < output.len() {
            let remaining = output.len() - offset;
            let mut temp = [0u8; 200];
            self.state.extract_bytes(&mut temp[..self.rate_bytes]);
            output[offset..].copy_from_slice(&temp[..remaining]);
            self.position = remaining;
        }
    }
}

impl Drop for KeccakSponge {
    fn drop(&mut self) {
        // State is zeroized by its own Drop impl
        self.position = 0;
        self.squeezed = false;
    }
}

// =============================================================================
// SHAKE128 (FIPS 202, Section 6.2)
// =============================================================================

/// SHAKE128 rate in bytes: (1600 - 256) / 8 = 168
pub const SHAKE128_RATE: usize = 168;

/// SHAKE128 extendable-output function
///
/// SHAKE128 provides 128-bit security and can produce any length output.
/// Uses rate r = 1344 bits (168 bytes), capacity c = 256 bits.
pub struct Shake128 {
    sponge: KeccakSponge,
}

impl Shake128 {
    /// Create a new SHAKE128 instance
    #[must_use]
    pub fn new() -> Self {
        // SHAKE uses suffix 0x1F = 0b00011111
        // This encodes the domain separation (0x0F) followed by the
        // first bits of the padding (0x10 for the '1' in 10*1)
        // Actually, for SHAKE the suffix is 0x1F which is:
        // - 4 bits of domain separation (1111 = 0xF)
        // - Then the padding starts with '1' making it 0x1F
        Self {
            sponge: KeccakSponge::new(SHAKE128_RATE, 0x1F),
        }
    }

    /// Absorb input data
    pub fn update(&mut self, data: &[u8]) {
        self.sponge.absorb(data);
    }

    /// Squeeze output bytes
    ///
    /// Can be called multiple times to produce arbitrarily long output.
    pub fn squeeze(&mut self, output: &mut [u8]) {
        self.sponge.squeeze(output);
    }

    /// One-shot: absorb and squeeze in a single call
    pub fn hash(input: &[u8], output: &mut [u8]) {
        let mut shake = Self::new();
        shake.update(input);
        shake.squeeze(output);
    }
}

impl Default for Shake128 {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// SHAKE256 (FIPS 202, Section 6.2)
// =============================================================================

/// SHAKE256 rate in bytes: (1600 - 512) / 8 = 136
pub const SHAKE256_RATE: usize = 136;

/// SHAKE256 extendable-output function
///
/// SHAKE256 provides 256-bit security and can produce any length output.
/// Uses rate r = 1088 bits (136 bytes), capacity c = 512 bits.
pub struct Shake256 {
    sponge: KeccakSponge,
}

impl Shake256 {
    /// Create a new SHAKE256 instance
    #[must_use]
    pub fn new() -> Self {
        Self {
            sponge: KeccakSponge::new(SHAKE256_RATE, 0x1F),
        }
    }

    /// Absorb input data
    pub fn update(&mut self, data: &[u8]) {
        self.sponge.absorb(data);
    }

    /// Squeeze output bytes
    ///
    /// Can be called multiple times to produce arbitrarily long output.
    pub fn squeeze(&mut self, output: &mut [u8]) {
        self.sponge.squeeze(output);
    }

    /// One-shot: absorb and squeeze in a single call
    pub fn hash(input: &[u8], output: &mut [u8]) {
        let mut shake = Self::new();
        shake.update(input);
        shake.squeeze(output);
    }
}

impl Default for Shake256 {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// SHA3 Hash Functions (for completeness)
// =============================================================================

/// SHA3-256 output size in bytes
pub const SHA3_256_OUTPUT_SIZE: usize = 32;

/// SHA3-256 rate in bytes: (1600 - 512) / 8 = 136
pub const SHA3_256_RATE: usize = 136;

/// SHA3-256 hash function
pub struct Sha3_256 {
    sponge: KeccakSponge,
}

impl Sha3_256 {
    /// Create a new SHA3-256 instance
    #[must_use]
    pub fn new() -> Self {
        // SHA-3 uses suffix 0x06 (domain separation for hash functions)
        Self {
            sponge: KeccakSponge::new(SHA3_256_RATE, 0x06),
        }
    }

    /// Update with input data
    pub fn update(&mut self, data: &[u8]) {
        self.sponge.absorb(data);
    }

    /// Finalize and return the 32-byte hash
    #[must_use]
    pub fn finalize(mut self) -> [u8; SHA3_256_OUTPUT_SIZE] {
        let mut output = [0u8; SHA3_256_OUTPUT_SIZE];
        self.sponge.squeeze(&mut output);
        output
    }

    /// One-shot hash function
    pub fn hash(input: &[u8]) -> [u8; SHA3_256_OUTPUT_SIZE] {
        let mut hasher = Self::new();
        hasher.update(input);
        hasher.finalize()
    }
}

impl Default for Sha3_256 {
    fn default() -> Self {
        Self::new()
    }
}

/// SHA3-512 output size in bytes
pub const SHA3_512_OUTPUT_SIZE: usize = 64;

/// SHA3-512 rate in bytes: (1600 - 1024) / 8 = 72
pub const SHA3_512_RATE: usize = 72;

/// SHA3-512 hash function
pub struct Sha3_512 {
    sponge: KeccakSponge,
}

impl Sha3_512 {
    /// Create a new SHA3-512 instance
    #[must_use]
    pub fn new() -> Self {
        Self {
            sponge: KeccakSponge::new(SHA3_512_RATE, 0x06),
        }
    }

    /// Update with input data
    pub fn update(&mut self, data: &[u8]) {
        self.sponge.absorb(data);
    }

    /// Finalize and return the 64-byte hash
    #[must_use]
    pub fn finalize(mut self) -> [u8; SHA3_512_OUTPUT_SIZE] {
        let mut output = [0u8; SHA3_512_OUTPUT_SIZE];
        self.sponge.squeeze(&mut output);
        output
    }

    /// One-shot hash function
    pub fn hash(input: &[u8]) -> [u8; SHA3_512_OUTPUT_SIZE] {
        let mut hasher = Self::new();
        hasher.update(input);
        hasher.finalize()
    }
}

impl Default for Sha3_512 {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Keccak-f[1600] Permutation Tests
    // =========================================================================

    /// Test the zero state permutation
    /// A known test vector: permuting all zeros should give a specific result
    #[test]
    fn test_keccak_permute_zero_state() {
        let mut state = KeccakState::new();
        state.permute();

        // After permuting zero state, lane[0] should be a specific value
        // This is from the Keccak reference
        // The exact values can be computed or verified against reference implementations
        // Zero input through Keccak-f[1600] produces:
        // Lane 0: 0xF1258F7940E1DDE7
        assert_eq!(state.lanes[0], 0xF1258F7940E1DDE7);
    }

    /// Test round constants are correct
    #[test]
    fn test_round_constants() {
        // First few round constants from FIPS 202
        assert_eq!(RC[0], 0x0000000000000001);
        assert_eq!(RC[1], 0x0000000000008082);
        assert_eq!(RC[2], 0x800000000000808a);
        assert_eq!(RC[23], 0x8000000080008008);
    }

    /// Test rotation offsets are correct
    #[test]
    fn test_rotation_offsets() {
        // r[0,0] = 0
        assert_eq!(ROTATION_OFFSETS[0], 0);
        // r[1,0] = 1
        assert_eq!(ROTATION_OFFSETS[1], 1);
        // r[2,0] = 62
        assert_eq!(ROTATION_OFFSETS[2], 62);
        // r[0,1] = 36
        assert_eq!(ROTATION_OFFSETS[5], 36);
    }

    // =========================================================================
    // SHAKE128 Test Vectors (from NIST)
    // =========================================================================

    /// SHAKE128 empty input test (NIST CAVP)
    #[test]
    fn test_shake128_empty() {
        let mut output = [0u8; 32];
        Shake128::hash(b"", &mut output);

        // SHAKE128("") with 256-bit output
        // From NIST test vectors
        let expected: [u8; 32] = [
            0x7f, 0x9c, 0x2b, 0xa4, 0xe8, 0x8f, 0x82, 0x7d, 0x61, 0x60, 0x45, 0x50, 0x76, 0x05,
            0x85, 0x3e, 0xd7, 0x3b, 0x80, 0x93, 0xf6, 0xef, 0xbc, 0x88, 0xeb, 0x1a, 0x6e, 0xac,
            0xfa, 0x66, 0xef, 0x26,
        ];
        assert_eq!(output, expected);
    }

    /// SHAKE128 with specific input
    #[test]
    fn test_shake128_abc() {
        let mut output = [0u8; 32];
        Shake128::hash(b"abc", &mut output);

        // SHAKE128("abc") first 32 bytes
        let expected: [u8; 32] = [
            0x58, 0x81, 0x09, 0x2d, 0xd8, 0x18, 0xbf, 0x5c, 0xf8, 0xa3, 0xdd, 0xb7, 0x93, 0xfb,
            0xcb, 0xa7, 0x40, 0x97, 0xd5, 0xc5, 0x26, 0xa6, 0xd3, 0x5f, 0x97, 0xb8, 0x33, 0x51,
            0x94, 0x0f, 0x2c, 0xc8,
        ];
        assert_eq!(output, expected);
    }

    /// SHAKE128 incremental test
    #[test]
    fn test_shake128_incremental() {
        // Hash "abc" all at once
        let mut output1 = [0u8; 64];
        Shake128::hash(b"abc", &mut output1);

        // Hash "abc" incrementally
        let mut shake = Shake128::new();
        shake.update(b"a");
        shake.update(b"b");
        shake.update(b"c");
        let mut output2 = [0u8; 64];
        shake.squeeze(&mut output2);

        assert_eq!(output1, output2);
    }

    /// SHAKE128 multiple squeeze test
    #[test]
    fn test_shake128_multiple_squeeze() {
        // Squeeze in one call
        let mut output1 = [0u8; 200];
        Shake128::hash(b"test", &mut output1);

        // Squeeze in multiple calls
        let mut shake = Shake128::new();
        shake.update(b"test");
        let mut output2 = [0u8; 200];
        shake.squeeze(&mut output2[..50]);
        shake.squeeze(&mut output2[50..100]);
        shake.squeeze(&mut output2[100..]);

        assert_eq!(output1, output2);
    }

    // =========================================================================
    // SHAKE256 Test Vectors (from NIST)
    // =========================================================================

    /// SHAKE256 empty input test
    #[test]
    fn test_shake256_empty() {
        let mut output = [0u8; 32];
        Shake256::hash(b"", &mut output);

        // SHAKE256("") with 256-bit output
        let expected: [u8; 32] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e,
            0xeb, 0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64,
            0x6e, 0xd5, 0x76, 0x2f,
        ];
        assert_eq!(output, expected);
    }

    /// SHAKE256 with specific input
    #[test]
    fn test_shake256_abc() {
        let mut output = [0u8; 32];
        Shake256::hash(b"abc", &mut output);

        // SHAKE256("abc") first 32 bytes
        let expected: [u8; 32] = [
            0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77, 0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4,
            0x11, 0x4d, 0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee, 0x4f, 0x94, 0xea, 0x37,
            0xe7, 0x8b, 0x57, 0x39,
        ];
        assert_eq!(output, expected);
    }

    /// SHAKE256 long output test (for XOF verification)
    #[test]
    fn test_shake256_long_output() {
        // Test that we can squeeze more than one block
        let mut output = [0u8; 512];
        Shake256::hash(b"", &mut output);

        // First 32 bytes should match empty test
        let expected_start: [u8; 32] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e,
            0xeb, 0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64,
            0x6e, 0xd5, 0x76, 0x2f,
        ];
        assert_eq!(&output[..32], &expected_start);
    }

    // =========================================================================
    // SHA3-256 Test Vectors (from NIST)
    // =========================================================================

    /// SHA3-256 empty input test
    #[test]
    fn test_sha3_256_empty() {
        let output = Sha3_256::hash(b"");

        // SHA3-256("")
        let expected: [u8; 32] = [
            0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61,
            0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b,
            0x80, 0xf8, 0x43, 0x4a,
        ];
        assert_eq!(output, expected);
    }

    /// SHA3-256 "abc" test
    #[test]
    fn test_sha3_256_abc() {
        let output = Sha3_256::hash(b"abc");

        // SHA3-256("abc")
        let expected: [u8; 32] = [
            0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3,
            0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b, 0x46, 0xbf, 0xe2, 0x45,
            0x11, 0x43, 0x15, 0x32,
        ];
        assert_eq!(output, expected);
    }

    // =========================================================================
    // SHA3-512 Test Vectors (from NIST)
    // =========================================================================

    /// SHA3-512 empty input test
    #[test]
    fn test_sha3_512_empty() {
        let output = Sha3_512::hash(b"");

        // SHA3-512("")
        let expected: [u8; 64] = [
            0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5, 0xc8, 0xb5, 0x67, 0xdc, 0x18, 0x5a,
            0x75, 0x6e, 0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59, 0xe0, 0xd1, 0xdc, 0xc1,
            0x47, 0x5c, 0x80, 0xa6, 0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c, 0x11, 0xe3,
            0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58, 0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3,
            0x01, 0x75, 0x85, 0x86, 0x28, 0x1d, 0xcd, 0x26,
        ];
        assert_eq!(output, expected);
    }

    /// SHA3-512 "abc" test
    #[test]
    fn test_sha3_512_abc() {
        let output = Sha3_512::hash(b"abc");

        // SHA3-512("abc")
        let expected: [u8; 64] = [
            0xb7, 0x51, 0x85, 0x0b, 0x1a, 0x57, 0x16, 0x8a, 0x56, 0x93, 0xcd, 0x92, 0x4b, 0x6b,
            0x09, 0x6e, 0x08, 0xf6, 0x21, 0x82, 0x74, 0x44, 0xf7, 0x0d, 0x88, 0x4f, 0x5d, 0x02,
            0x40, 0xd2, 0x71, 0x2e, 0x10, 0xe1, 0x16, 0xe9, 0x19, 0x2a, 0xf3, 0xc9, 0x1a, 0x7e,
            0xc5, 0x76, 0x47, 0xe3, 0x93, 0x40, 0x57, 0x34, 0x0b, 0x4c, 0xf4, 0x08, 0xd5, 0xa5,
            0x65, 0x92, 0xf8, 0x27, 0x4e, 0xec, 0x53, 0xf0,
        ];
        assert_eq!(output, expected);
    }

    // =========================================================================
    // Edge Cases and Stress Tests
    // =========================================================================

    /// Test absorbing exactly one block
    #[test]
    fn test_shake256_one_block() {
        // SHAKE256 rate is 136 bytes
        let input = [0x42u8; SHAKE256_RATE];
        let mut output = [0u8; 32];
        Shake256::hash(&input, &mut output);

        // Should not panic and produce valid output
        assert_ne!(output, [0u8; 32]);
    }

    /// Test absorbing more than one block
    #[test]
    fn test_shake128_multi_block() {
        // SHAKE128 rate is 168 bytes, absorb 500 bytes
        let input = [0xABu8; 500];
        let mut output = [0u8; 64];
        Shake128::hash(&input, &mut output);

        // Should produce consistent output
        let mut output2 = [0u8; 64];
        Shake128::hash(&input, &mut output2);
        assert_eq!(output, output2);
    }

    /// Test single byte inputs
    #[test]
    fn test_shake256_single_bytes() {
        for byte in 0..=255u8 {
            let mut output = [0u8; 16];
            Shake256::hash(&[byte], &mut output);
            // Just verify it doesn't panic
        }
    }

    /// Test state zeroization
    #[test]
    fn test_state_zeroization() {
        let mut state = KeccakState::new();
        state.lanes[0] = 0xDEADBEEF;
        drop(state);
        // Cannot directly verify zeroization, but this tests the Drop impl runs
    }
}
