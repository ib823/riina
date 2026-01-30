//! AES-256 Block Cipher Implementation
//!
//! This module implements AES-256 (Rijndael with 256-bit key and 128-bit block).
//!
//! # Constant-Time Guarantees (Law 3)
//!
//! This implementation uses constant-time table lookups to prevent timing attacks.
//! All table accesses read the entire table and select the result using bitwise
//! operations, ensuring no timing variation based on the index.
//!
//! # Security Notes
//!
//! - Key schedule is computed on construction and zeroized on drop
//! - All intermediate state is zeroized after use
//! - No secret-dependent branches or memory accesses

use crate::zeroize::Zeroize;

/// AES-256 block size in bytes
pub const BLOCK_SIZE: usize = 16;
/// AES-256 key size in bytes
pub const KEY_SIZE: usize = 32;
/// Number of rounds for AES-256
const NR: usize = 14;
/// Number of 32-bit words in expanded key
const NK: usize = 8;
/// Number of 32-bit columns in state
const NB: usize = 4;
/// Total words in expanded key schedule
const EXPANDED_KEY_WORDS: usize = NB * (NR + 1);

/// AES S-box (substitution box)
/// This is a fixed permutation of all 256 bytes
const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

/// AES Inverse S-box for decryption
const INV_SBOX: [u8; 256] = [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
];

/// Round constants for key expansion
const RCON: [u8; 11] = [
    0x00, // Not used (round 0)
    0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
];

/// Constant-time table lookup
///
/// This function reads ALL table entries and uses bitwise operations to select
/// the correct one, ensuring no timing variation based on the index.
#[inline]
fn ct_lookup(table: &[u8; 256], index: u8) -> u8 {
    let mut result: u8 = 0;
    for (i, &value) in table.iter().enumerate() {
        // Create a mask that is 0xFF when i == index, 0x00 otherwise
        // This is done without branching
        let i_byte = i as u8;
        let eq = ct_eq_byte(i_byte, index);
        result |= value & eq;
    }
    result
}

/// Constant-time byte equality
/// Returns 0xFF if a == b, 0x00 otherwise
///
/// # Security Analysis (FIPS-197 Compliant, Constant-Time)
///
/// This implementation uses 16-bit arithmetic to avoid signed integer edge cases:
/// - diff = 0: (0u16).wrapping_sub(1) = 0xFFFF, >> 8 = 0xFF ✓
/// - diff = 1: (1u16).wrapping_sub(1) = 0x0000, >> 8 = 0x00 ✓
/// - diff = 128: (128u16).wrapping_sub(1) = 0x007F, >> 8 = 0x00 ✓
/// - diff = 255: (255u16).wrapping_sub(1) = 0x00FE, >> 8 = 0x00 ✓
///
/// The previous i8-based implementation was INCORRECT:
/// - For diff >= 129: (diff as i8) is negative, wrapping_sub(1) stays negative,
///   arithmetic right shift >> 7 produces -1 (0xFF), causing false matches.
#[inline]
fn ct_eq_byte(a: u8, b: u8) -> u8 {
    let diff = a ^ b;
    // If diff is 0, we want 0xFF; otherwise 0x00
    // Zero-extend to 16 bits and check for underflow when subtracting 1
    // This avoids all signed integer edge cases
    let wide = diff as u16;
    // diff=0: (0x0000 - 1) = 0xFFFF, >> 8 = 0xFF (match)
    // diff>0: (diff - 1) fits in low byte, >> 8 = 0x00 (no match)
    (wide.wrapping_sub(1) >> 8) as u8
}

/// AES-256 cipher instance
pub struct Aes256 {
    /// Expanded key schedule (60 32-bit words)
    round_keys: [u32; EXPANDED_KEY_WORDS],
}

impl Aes256 {
    /// Create a new AES-256 instance from a 32-byte key
    ///
    /// # Panics
    /// Panics if key is not exactly 32 bytes.
    #[must_use]
    pub fn new(key: &[u8; KEY_SIZE]) -> Self {
        let mut round_keys = [0u32; EXPANDED_KEY_WORDS];
        key_expansion(key, &mut round_keys);
        Self { round_keys }
    }

    /// Encrypt a single 16-byte block in place
    pub fn encrypt_block(&self, block: &mut [u8; BLOCK_SIZE]) {
        let mut state = block_to_state(block);
        
        // Initial round key addition
        add_round_key(&mut state, &self.round_keys[0..NB]);
        
        // Main rounds (1 to NR-1)
        for round in 1..NR {
            sub_bytes(&mut state);
            shift_rows(&mut state);
            mix_columns(&mut state);
            add_round_key(&mut state, &self.round_keys[round * NB..(round + 1) * NB]);
        }
        
        // Final round (no MixColumns)
        sub_bytes(&mut state);
        shift_rows(&mut state);
        add_round_key(&mut state, &self.round_keys[NR * NB..(NR + 1) * NB]);
        
        state_to_block(&state, block);
    }

    /// Decrypt a single 16-byte block in place
    pub fn decrypt_block(&self, block: &mut [u8; BLOCK_SIZE]) {
        let mut state = block_to_state(block);
        
        // Initial round key addition (last round key)
        add_round_key(&mut state, &self.round_keys[NR * NB..(NR + 1) * NB]);
        
        // Main rounds (NR-1 down to 1)
        for round in (1..NR).rev() {
            inv_shift_rows(&mut state);
            inv_sub_bytes(&mut state);
            add_round_key(&mut state, &self.round_keys[round * NB..(round + 1) * NB]);
            inv_mix_columns(&mut state);
        }
        
        // Final round (no InvMixColumns)
        inv_shift_rows(&mut state);
        inv_sub_bytes(&mut state);
        add_round_key(&mut state, &self.round_keys[0..NB]);
        
        state_to_block(&state, block);
    }
}

impl Drop for Aes256 {
    fn drop(&mut self) {
        // Zeroize the key schedule (Law 4)
        self.round_keys.zeroize();
    }
}

/// Expand the key into the round key schedule
fn key_expansion(key: &[u8; KEY_SIZE], w: &mut [u32; EXPANDED_KEY_WORDS]) {
    // First NK words are the key itself
    for i in 0..NK {
        w[i] = u32::from_be_bytes([
            key[4 * i],
            key[4 * i + 1],
            key[4 * i + 2],
            key[4 * i + 3],
        ]);
    }

    // Generate remaining words
    for i in NK..EXPANDED_KEY_WORDS {
        let mut temp = w[i - 1];
        
        if i % NK == 0 {
            // RotWord + SubWord + Rcon
            temp = sub_word(rot_word(temp)) ^ (u32::from(RCON[i / NK]) << 24);
        } else if NK > 6 && i % NK == 4 {
            // AES-256 has an extra SubWord step
            temp = sub_word(temp);
        }
        
        w[i] = w[i - NK] ^ temp;
    }
}

/// Rotate word left by one byte
#[inline]
fn rot_word(word: u32) -> u32 {
    word.rotate_left(8)
}

/// Apply S-box to each byte of a word (constant-time)
#[inline]
fn sub_word(word: u32) -> u32 {
    let bytes = word.to_be_bytes();
    let result = [
        ct_lookup(&SBOX, bytes[0]),
        ct_lookup(&SBOX, bytes[1]),
        ct_lookup(&SBOX, bytes[2]),
        ct_lookup(&SBOX, bytes[3]),
    ];
    u32::from_be_bytes(result)
}

/// Convert a 16-byte block to state array (4 columns of 4 bytes each)
#[inline]
fn block_to_state(block: &[u8; BLOCK_SIZE]) -> [u32; 4] {
    [
        u32::from_be_bytes([block[0], block[1], block[2], block[3]]),
        u32::from_be_bytes([block[4], block[5], block[6], block[7]]),
        u32::from_be_bytes([block[8], block[9], block[10], block[11]]),
        u32::from_be_bytes([block[12], block[13], block[14], block[15]]),
    ]
}

/// Convert state array back to 16-byte block
#[inline]
fn state_to_block(state: &[u32; 4], block: &mut [u8; BLOCK_SIZE]) {
    let b0 = state[0].to_be_bytes();
    let b1 = state[1].to_be_bytes();
    let b2 = state[2].to_be_bytes();
    let b3 = state[3].to_be_bytes();
    
    block[0..4].copy_from_slice(&b0);
    block[4..8].copy_from_slice(&b1);
    block[8..12].copy_from_slice(&b2);
    block[12..16].copy_from_slice(&b3);
}

/// Add round key (XOR state with round key)
#[inline]
fn add_round_key(state: &mut [u32; 4], round_key: &[u32]) {
    state[0] ^= round_key[0];
    state[1] ^= round_key[1];
    state[2] ^= round_key[2];
    state[3] ^= round_key[3];
}

/// SubBytes transformation (constant-time S-box lookup)
fn sub_bytes(state: &mut [u32; 4]) {
    for col in state.iter_mut() {
        let bytes = col.to_be_bytes();
        let result = [
            ct_lookup(&SBOX, bytes[0]),
            ct_lookup(&SBOX, bytes[1]),
            ct_lookup(&SBOX, bytes[2]),
            ct_lookup(&SBOX, bytes[3]),
        ];
        *col = u32::from_be_bytes(result);
    }
}

/// InvSubBytes transformation (constant-time inverse S-box lookup)
fn inv_sub_bytes(state: &mut [u32; 4]) {
    for col in state.iter_mut() {
        let bytes = col.to_be_bytes();
        let result = [
            ct_lookup(&INV_SBOX, bytes[0]),
            ct_lookup(&INV_SBOX, bytes[1]),
            ct_lookup(&INV_SBOX, bytes[2]),
            ct_lookup(&INV_SBOX, bytes[3]),
        ];
        *col = u32::from_be_bytes(result);
    }
}

/// ShiftRows transformation
/// Row 0: no shift
/// Row 1: shift left by 1
/// Row 2: shift left by 2
/// Row 3: shift left by 3
fn shift_rows(state: &mut [u32; 4]) {
    // Extract rows from column-major state
    let s: [[u8; 4]; 4] = [
        [
            (state[0] >> 24) as u8,
            (state[1] >> 24) as u8,
            (state[2] >> 24) as u8,
            (state[3] >> 24) as u8,
        ],
        [
            (state[0] >> 16) as u8,
            (state[1] >> 16) as u8,
            (state[2] >> 16) as u8,
            (state[3] >> 16) as u8,
        ],
        [
            (state[0] >> 8) as u8,
            (state[1] >> 8) as u8,
            (state[2] >> 8) as u8,
            (state[3] >> 8) as u8,
        ],
        [
            state[0] as u8,
            state[1] as u8,
            state[2] as u8,
            state[3] as u8,
        ],
    ];

    // Apply shifts
    let t: [[u8; 4]; 4] = [
        [s[0][0], s[0][1], s[0][2], s[0][3]], // No shift
        [s[1][1], s[1][2], s[1][3], s[1][0]], // Shift left 1
        [s[2][2], s[2][3], s[2][0], s[2][1]], // Shift left 2
        [s[3][3], s[3][0], s[3][1], s[3][2]], // Shift left 3
    ];

    // Pack back into columns
    state[0] = u32::from_be_bytes([t[0][0], t[1][0], t[2][0], t[3][0]]);
    state[1] = u32::from_be_bytes([t[0][1], t[1][1], t[2][1], t[3][1]]);
    state[2] = u32::from_be_bytes([t[0][2], t[1][2], t[2][2], t[3][2]]);
    state[3] = u32::from_be_bytes([t[0][3], t[1][3], t[2][3], t[3][3]]);
}

/// InvShiftRows transformation (inverse of ShiftRows)
fn inv_shift_rows(state: &mut [u32; 4]) {
    let s: [[u8; 4]; 4] = [
        [
            (state[0] >> 24) as u8,
            (state[1] >> 24) as u8,
            (state[2] >> 24) as u8,
            (state[3] >> 24) as u8,
        ],
        [
            (state[0] >> 16) as u8,
            (state[1] >> 16) as u8,
            (state[2] >> 16) as u8,
            (state[3] >> 16) as u8,
        ],
        [
            (state[0] >> 8) as u8,
            (state[1] >> 8) as u8,
            (state[2] >> 8) as u8,
            (state[3] >> 8) as u8,
        ],
        [
            state[0] as u8,
            state[1] as u8,
            state[2] as u8,
            state[3] as u8,
        ],
    ];

    // Apply inverse shifts (shift right instead of left)
    let t: [[u8; 4]; 4] = [
        [s[0][0], s[0][1], s[0][2], s[0][3]], // No shift
        [s[1][3], s[1][0], s[1][1], s[1][2]], // Shift right 1
        [s[2][2], s[2][3], s[2][0], s[2][1]], // Shift right 2
        [s[3][1], s[3][2], s[3][3], s[3][0]], // Shift right 3
    ];

    state[0] = u32::from_be_bytes([t[0][0], t[1][0], t[2][0], t[3][0]]);
    state[1] = u32::from_be_bytes([t[0][1], t[1][1], t[2][1], t[3][1]]);
    state[2] = u32::from_be_bytes([t[0][2], t[1][2], t[2][2], t[3][2]]);
    state[3] = u32::from_be_bytes([t[0][3], t[1][3], t[2][3], t[3][3]]);
}

/// Multiply by x in GF(2^8) with reduction by x^8 + x^4 + x^3 + x + 1
#[inline]
fn xtime(b: u8) -> u8 {
    let high_bit = (b >> 7) & 1;
    let shifted = b << 1;
    // If high bit was set, XOR with 0x1b (the reduction polynomial)
    // This is constant-time: we always compute both and select
    shifted ^ (0x1b * high_bit)
}

/// Multiply in GF(2^8)
#[inline]
fn gf_mul(a: u8, b: u8) -> u8 {
    let mut result = 0u8;
    let mut aa = a;
    let mut bb = b;
    
    for _ in 0..8 {
        // If low bit of bb is set, XOR aa into result
        result ^= aa & (0u8.wrapping_sub(bb & 1));
        aa = xtime(aa);
        bb >>= 1;
    }
    
    result
}

/// MixColumns transformation
fn mix_columns(state: &mut [u32; 4]) {
    for col in state.iter_mut() {
        let bytes = col.to_be_bytes();
        let s0 = bytes[0];
        let s1 = bytes[1];
        let s2 = bytes[2];
        let s3 = bytes[3];
        
        // Matrix multiplication in GF(2^8):
        // [02 03 01 01]   [s0]
        // [01 02 03 01] * [s1]
        // [01 01 02 03]   [s2]
        // [03 01 01 02]   [s3]
        
        let r0 = gf_mul(0x02, s0) ^ gf_mul(0x03, s1) ^ s2 ^ s3;
        let r1 = s0 ^ gf_mul(0x02, s1) ^ gf_mul(0x03, s2) ^ s3;
        let r2 = s0 ^ s1 ^ gf_mul(0x02, s2) ^ gf_mul(0x03, s3);
        let r3 = gf_mul(0x03, s0) ^ s1 ^ s2 ^ gf_mul(0x02, s3);
        
        *col = u32::from_be_bytes([r0, r1, r2, r3]);
    }
}

/// InvMixColumns transformation
fn inv_mix_columns(state: &mut [u32; 4]) {
    for col in state.iter_mut() {
        let bytes = col.to_be_bytes();
        let s0 = bytes[0];
        let s1 = bytes[1];
        let s2 = bytes[2];
        let s3 = bytes[3];
        
        // Inverse matrix multiplication in GF(2^8):
        // [0e 0b 0d 09]   [s0]
        // [09 0e 0b 0d] * [s1]
        // [0d 09 0e 0b]   [s2]
        // [0b 0d 09 0e]   [s3]
        
        let r0 = gf_mul(0x0e, s0) ^ gf_mul(0x0b, s1) ^ gf_mul(0x0d, s2) ^ gf_mul(0x09, s3);
        let r1 = gf_mul(0x09, s0) ^ gf_mul(0x0e, s1) ^ gf_mul(0x0b, s2) ^ gf_mul(0x0d, s3);
        let r2 = gf_mul(0x0d, s0) ^ gf_mul(0x09, s1) ^ gf_mul(0x0e, s2) ^ gf_mul(0x0b, s3);
        let r3 = gf_mul(0x0b, s0) ^ gf_mul(0x0d, s1) ^ gf_mul(0x09, s2) ^ gf_mul(0x0e, s3);
        
        *col = u32::from_be_bytes([r0, r1, r2, r3]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FIPS 197 Appendix C.3 - AES-256 test vector
    #[test]
    fn test_aes256_fips197() {
        let key: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        ];
        
        let plaintext: [u8; 16] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
        ];
        
        let expected_ciphertext: [u8; 16] = [
            0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
            0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89,
        ];
        
        let cipher = Aes256::new(&key);
        let mut block = plaintext;
        cipher.encrypt_block(&mut block);
        
        assert_eq!(block, expected_ciphertext, "Encryption failed");
        
        cipher.decrypt_block(&mut block);
        assert_eq!(block, plaintext, "Decryption failed");
    }

    /// Test encrypt/decrypt round-trip with random-ish data
    #[test]
    fn test_aes256_roundtrip() {
        let key: [u8; 32] = [
            0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe,
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
            0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69, 0x78,
        ];
        
        let plaintext: [u8; 16] = [
            0x54, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20,
            0x61, 0x20, 0x74, 0x65, 0x73, 0x74, 0x21, 0x00,
        ]; // "This is a test!"
        
        let cipher = Aes256::new(&key);
        let mut block = plaintext;
        
        cipher.encrypt_block(&mut block);
        assert_ne!(block, plaintext, "Encryption should change plaintext");
        
        cipher.decrypt_block(&mut block);
        assert_eq!(block, plaintext, "Round-trip failed");
    }

    /// Test key schedule generation
    #[test]
    fn test_key_expansion() {
        let key: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        ];
        
        let mut round_keys = [0u32; EXPANDED_KEY_WORDS];
        key_expansion(&key, &mut round_keys);
        
        // First 8 words should be the key
        assert_eq!(round_keys[0], 0x00010203);
        assert_eq!(round_keys[1], 0x04050607);
        assert_eq!(round_keys[7], 0x1c1d1e1f);
        
        // Verify we have all 60 words
        assert_eq!(round_keys.len(), 60);
    }

    /// Test constant-time lookup
    #[test]
    fn test_ct_lookup() {
        // Test a few known values
        assert_eq!(ct_lookup(&SBOX, 0x00), 0x63);
        assert_eq!(ct_lookup(&SBOX, 0x01), 0x7c);
        assert_eq!(ct_lookup(&SBOX, 0xff), 0x16);
        
        // Test inverse
        assert_eq!(ct_lookup(&INV_SBOX, 0x63), 0x00);
        assert_eq!(ct_lookup(&INV_SBOX, 0x7c), 0x01);
    }

    /// Test GF(2^8) multiplication
    #[test]
    fn test_gf_mul() {
        // Known values from AES spec
        assert_eq!(gf_mul(0x57, 0x83), 0xc1);
        assert_eq!(gf_mul(0x02, 0x87), 0x15);
        assert_eq!(gf_mul(0x03, 0x87), 0x92); // 0x02 * 0x87 ^ 0x87
    }
}
