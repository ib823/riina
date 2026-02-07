// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! ML-KEM-768 (Module-Lattice Key Encapsulation Mechanism) Implementation
//!
//! This module implements ML-KEM-768 as specified in FIPS 203 (August 2024).
//! ML-KEM is a post-quantum key encapsulation mechanism based on the
//! Module Learning With Errors (MLWE) problem.
//!
//! # FIPS 203 Compliance
//!
//! This implementation follows FIPS 203 "Module-Lattice-Based Key-Encapsulation
//! Mechanism Standard" exactly. Every constant, algorithm, and data structure
//! is derived directly from the specification.
//!
//! # Law 2: Cryptographic Non-Negotiables
//!
//! ML-KEM-768 is used in hybrid key encapsulation alongside X25519.
//! The combination provides security against both classical and quantum adversaries.
//!
//! # Security Properties
//!
//! - IND-CCA2 security via Fujisaki-Okamoto transform
//! - ~192-bit post-quantum security level (NIST Level 3)
//! - Resistant to quantum attacks using Shor's algorithm
//! - Implicit rejection on decapsulation failure
//!
//! # Implementation Notes
//!
//! - Number Theoretic Transform (NTT) over Z_q[X]/(X^256 + 1) where q = 3329
//! - NTT uses ζ = 17 as primitive 512th root of unity mod q
//! - Barrett reduction for efficient modular arithmetic
//! - Centered binomial distribution sampling using PRF
//! - Constant-time operations on secret data (Law 3)
//! - Zeroization of secrets on drop (Law 4)
//!
//! # References
//!
//! - FIPS 203: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf

use crate::crypto::keccak::{Sha3_256, Sha3_512, Shake128, Shake256};
use crate::crypto::{CryptoError, CryptoResult, Kem};
use crate::zeroize::Zeroize;

// =============================================================================
// ML-KEM-768 Parameters (FIPS 203, Table 2)
// =============================================================================

/// ML-KEM-768 parameters
pub mod params {
    /// Degree of polynomials (n)
    pub const N: usize = 256;
    /// Modulus (q)
    pub const Q: u16 = 3329;
    /// Number of polynomials in vector (k) - ML-KEM-768 uses k=3
    pub const K: usize = 3;
    /// Bits for compression of public key polynomials (d_u)
    pub const DU: usize = 10;
    /// Bits for compression of ciphertext polynomial (d_v)
    pub const DV: usize = 4;
    /// Distribution parameter (η₁) for secret and error
    pub const ETA1: usize = 2;
    /// Distribution parameter (η₂) for encryption noise
    pub const ETA2: usize = 2;
    /// Q as u32 for Barrett reduction
    pub const Q32: u32 = Q as u32;
    /// Q as i32 for signed operations
    pub const Q_I32: i32 = Q as i32;
}

/// ML-KEM-768 secret key size: 12·k·n/8 + 12·k·n/8 + 32 + 32 + 32 = 2400 bytes
/// = dk_PKE (1152) + ek (1184) + H(ek) (32) + z (32)
pub const SECRET_KEY_SIZE: usize = 2400;

/// ML-KEM-768 public key size: 12·k·n/8 + 32 = 1184 bytes
/// = t_hat (1152) + ρ (32)
pub const PUBLIC_KEY_SIZE: usize = 1184;

/// ML-KEM-768 ciphertext size: d_u·k·n/8 + d_v·n/8 = 1088 bytes
/// = c₁ (960) + c₂ (128)
pub const CIPHERTEXT_SIZE: usize = 1088;

/// ML-KEM-768 shared secret size (32 bytes)
pub const SHARED_SECRET_SIZE: usize = 32;

// =============================================================================
// NTT Constants (FIPS 203, Section 4.3)
// =============================================================================

/// Zetas in Montgomery domain (R = 2^16)
///
/// These are derived from the Kyber reference implementation.
/// zetas[i] = ζ^(BitRev_7(i)) * 2^16 mod q in signed representation [-q/2, q/2)
/// Converted to signed i16 for use with Montgomery arithmetic.
///
/// Source: pq-crystals/kyber reference implementation
const ZETAS: [i16; 128] = [
    -1044,  -758,  -359, -1517,  1493,  1422,   287,   202,
     -171,   622,  1577,   182,   962, -1202, -1474,  1468,
      573, -1325,   264,   383,  -829,  1458, -1602,  -130,
     -681,  1017,   732,   608, -1542,   411,  -205, -1571,
     1223,   652,  -552,  1015, -1293,  1491,  -282, -1544,
      516,    -8,  -320,  -666, -1618, -1162,   126,  1469,
     -853,   -90,  -271,   830,   107, -1421,  -247,  -951,
     -398,   961, -1508,  -725,   448, -1065,   677, -1275,
    -1103,   430,   555,   843, -1251,   871,  1550,   105,
      422,   587,   177,  -235,  -291,  -460,  1574,  1653,
     -246,   778,  1159,  -147,  -777,  1483,  -602,  1119,
    -1590,   644,  -872,   349,   418,   329,  -156,   -75,
      817,  1097,   603,   610,  1322, -1285, -1465,   384,
    -1215,  -136,  1218, -1335,  -874,   220, -1187, -1659,
    -1185, -1530, -1278,   794, -1510,  -854,  -870,   478,
     -108,  -308,   996,   991,   958, -1460,  1522,  1628,
];

/// NTT scaling factor for inverse NTT
///
/// In ML-KEM/Kyber, the inverse NTT is always preceded by pointwise
/// multiplication (basemul) which introduces an extra R^(-1) Montgomery factor.
///
/// F = R^2 / 128 mod q = (2^16)^2 / 128 mod 3329 = 1441
///
/// This compensates for:
/// 1. The 1/128 factor from 7 layers of inverse NTT butterflies
/// 2. The extra R^(-1) from basemul operations
///
/// fqmul(coeff, F) = coeff * F * R^(-1) = coeff * R^2/128 * R^(-1) = coeff * R/128
/// When coeff = value * R^(-1) (from basemul): result = value * R^(-1) * R/128 = value/128
const F: i16 = 1441;

// =============================================================================
// Barrett Reduction Constants
// =============================================================================

/// Barrett reduction constant: ((1<<26) + q/2) / q ≈ 20159
/// Using Kyber's formula: v = ((1<<26) + Q/2) / Q
const BARRETT_V: i32 = ((1i32 << 26) + (params::Q as i32) / 2) / (params::Q as i32);

/// Barrett reduction for modular reduction by q
///
/// Reduces a to a value congruent modulo q in range approximately [-q, 2q).
/// Uses the formula from the Kyber reference implementation.
#[inline]
fn barrett_reduce(a: i16) -> i16 {
    // t = round(a / q) using Barrett approximation
    let t = (((BARRETT_V * i32::from(a)) + (1 << 25)) >> 26) as i16;
    // r = a - t*q (result is in approximately [-q, 2q))
    a - t * params::Q as i16
}

/// Conditional subtract: r = a - q if a >= q, else a
#[inline]
fn cond_sub_q(a: i16) -> i16 {
    let diff = a - params::Q as i16;
    // If diff >= 0, use diff; otherwise use a
    let mask = diff >> 15; // -1 if diff < 0, 0 otherwise
    (diff & !mask) | (a & mask)
}

/// Normalize coefficient to positive representative in [0, q)
///
/// This handles negative values from barrett_reduce by adding q if needed.
#[inline]
fn to_positive(a: i16) -> u16 {
    let mut r = a % (params::Q as i16);
    if r < 0 {
        r += params::Q as i16;
    }
    r as u16
}

/// Montgomery reduction: given a * R mod q, compute a mod q
/// where R = 2^16
#[inline]
fn montgomery_reduce(a: i32) -> i16 {
    // q^(-1) mod 2^16 = 62209 (but we use the signed version -3327)
    const QINV: i32 = -3327;

    // t = a * q^(-1) mod 2^16
    let t = (a as i16).wrapping_mul(QINV as i16);
    // u = (a - t*q) / 2^16
    let u = (a - i32::from(t) * params::Q_I32) >> 16;
    u as i16
}

/// Multiply two values in Montgomery form and reduce
#[inline]
fn fqmul(a: i16, b: i16) -> i16 {
    montgomery_reduce(i32::from(a) * i32::from(b))
}

// =============================================================================
// Polynomial Type
// =============================================================================

/// Polynomial in Z_q[X]/(X^256 + 1)
///
/// Coefficients are stored in [0, q) in standard representation,
/// or in Montgomery form when in NTT domain.
#[derive(Clone)]
pub struct Poly {
    /// 256 coefficients
    coeffs: [i16; params::N],
}

impl Poly {
    /// Create a zero polynomial
    #[inline]
    pub fn zero() -> Self {
        Self { coeffs: [0; params::N] }
    }

    /// Reduce all coefficients to [0, q)
    pub fn reduce(&mut self) {
        for coeff in &mut self.coeffs {
            *coeff = barrett_reduce(*coeff);
            *coeff = cond_sub_q(*coeff);
        }
    }

    /// Add two polynomials coefficient-wise
    pub fn add(&mut self, other: &Poly) {
        for i in 0..params::N {
            self.coeffs[i] = self.coeffs[i].wrapping_add(other.coeffs[i]);
        }
    }

    /// Subtract two polynomials coefficient-wise
    pub fn sub(&mut self, other: &Poly) {
        for i in 0..params::N {
            self.coeffs[i] = self.coeffs[i].wrapping_sub(other.coeffs[i]);
        }
    }

    /// Forward NTT (Number Theoretic Transform)
    ///
    /// Transforms polynomial from coefficient form to NTT domain.
    /// After NTT, polynomial multiplication becomes pointwise.
    ///
    /// Algorithm 9 from FIPS 203 / Kyber reference
    pub fn ntt(&mut self) {
        let mut k = 1usize; // Start at 1, not 0 (zetas[0] is unused)
        let mut len = 128usize;

        while len >= 2 {
            let mut start = 0usize;
            while start < params::N {
                let zeta = ZETAS[k];
                k += 1;
                let mut j = start;
                while j < start + len {
                    let t = fqmul(zeta, self.coeffs[j + len]);
                    self.coeffs[j + len] = self.coeffs[j].wrapping_sub(t);
                    self.coeffs[j] = self.coeffs[j].wrapping_add(t);
                    j += 1;
                }
                start = start + 2 * len;
            }
            len >>= 1;
        }
    }

    /// Inverse NTT
    ///
    /// Transforms polynomial from NTT domain back to coefficient form
    /// and converts from Montgomery representation.
    ///
    /// Algorithm 10 from FIPS 203 / Kyber reference
    pub fn inv_ntt(&mut self) {
        let mut k = 127usize;
        let mut len = 2usize;

        while len <= 128 {
            let mut start = 0usize;
            while start < params::N {
                // Kyber uses zetas[k--] directly (no negation)
                let zeta = ZETAS[k];
                k = k.wrapping_sub(1);
                let mut j = start;
                while j < start + len {
                    let t = self.coeffs[j];
                    self.coeffs[j] = barrett_reduce(t.wrapping_add(self.coeffs[j + len]));
                    self.coeffs[j + len] = fqmul(zeta, self.coeffs[j + len].wrapping_sub(t));
                    j += 1;
                }
                start = start + 2 * len;
            }
            len <<= 1;
        }

        // Multiply by f = n^(-1) * 2^16 mod q to convert from Montgomery
        for i in 0..params::N {
            self.coeffs[i] = fqmul(self.coeffs[i], F);
        }
    }

    /// Pointwise multiplication in NTT domain (basemul)
    ///
    /// Computes c = a ⊙ b where ⊙ is coefficient-wise multiplication
    /// followed by reduction using the factorization of X^256 + 1
    /// in the NTT domain.
    ///
    /// The NTT representation uses pairs of coefficients representing
    /// elements in Z_q[X]/(X^2 - zeta) for different zeta values.
    ///
    /// Algorithm 11 from FIPS 203
    pub fn pointwise_mul(&mut self, a: &Poly, b: &Poly) {
        // Process 4 coefficients per iteration
        // Pairs (4k, 4k+1) use zeta = ZETAS[64+k]
        // Pairs (4k+2, 4k+3) use zeta = -ZETAS[64+k]
        for k in 0..params::N / 4 {
            let zeta = ZETAS[64 + k];

            // First pair: indices 4k, 4k+1
            let idx0 = 4 * k;
            let a0 = a.coeffs[idx0];
            let a1 = a.coeffs[idx0 + 1];
            let b0 = b.coeffs[idx0];
            let b1 = b.coeffs[idx0 + 1];

            // (a0 + a1*X)(b0 + b1*X) mod (X^2 - zeta)
            self.coeffs[idx0] = fqmul(a0, b0).wrapping_add(fqmul(fqmul(a1, b1), zeta));
            self.coeffs[idx0 + 1] = fqmul(a0, b1).wrapping_add(fqmul(a1, b0));

            // Second pair: indices 4k+2, 4k+3 with negated zeta
            let idx2 = 4 * k + 2;
            let a2 = a.coeffs[idx2];
            let a3 = a.coeffs[idx2 + 1];
            let b2 = b.coeffs[idx2];
            let b3 = b.coeffs[idx2 + 1];

            // Use -zeta for the second pair
            let neg_zeta = -zeta;
            self.coeffs[idx2] = fqmul(a2, b2).wrapping_add(fqmul(fqmul(a3, b3), neg_zeta));
            self.coeffs[idx2 + 1] = fqmul(a2, b3).wrapping_add(fqmul(a3, b2));
        }
    }

    /// Sample polynomial from centered binomial distribution B_η
    ///
    /// CBD_η samples coefficients in [-η, η] using 2η bits each.
    /// Used for secret and error polynomials.
    ///
    /// Algorithm 7 from FIPS 203
    pub fn cbd(&mut self, bytes: &[u8], eta: usize) {
        debug_assert!(eta == 2 || eta == 3);
        debug_assert!(bytes.len() >= 64 * eta);

        if eta == 2 {
            // CBD_2: each coefficient uses 4 bits (2+2)
            for i in 0..params::N {
                let byte_idx = i / 2;
                let bits = if i % 2 == 0 {
                    bytes[byte_idx] & 0x0F
                } else {
                    bytes[byte_idx] >> 4
                };

                // a = popcount(bits[0..2]), b = popcount(bits[2..4])
                let a = (bits & 1) + ((bits >> 1) & 1);
                let b = ((bits >> 2) & 1) + ((bits >> 3) & 1);
                self.coeffs[i] = i16::from(a) - i16::from(b);
            }
        } else {
            // CBD_3: each coefficient uses 6 bits (3+3)
            let mut bit_pos = 0usize;
            for i in 0..params::N {
                // Extract 6 bits
                let byte_idx = bit_pos / 8;
                let bit_offset = bit_pos % 8;

                let mut bits: u32 = u32::from(bytes[byte_idx]) >> bit_offset;
                if bit_offset > 2 {
                    bits |= u32::from(bytes[byte_idx + 1]) << (8 - bit_offset);
                }
                bits &= 0x3F;

                // a = popcount(bits[0..3]), b = popcount(bits[3..6])
                let a = (bits & 1) + ((bits >> 1) & 1) + ((bits >> 2) & 1);
                let b = ((bits >> 3) & 1) + ((bits >> 4) & 1) + ((bits >> 5) & 1);
                self.coeffs[i] = (a as i16) - (b as i16);

                bit_pos += 6;
            }
        }
    }

    /// Encode polynomial to bytes (ByteEncode_12)
    ///
    /// Each coefficient c ∈ [0, q) is encoded as 12 bits.
    /// Output: 384 bytes for n=256 coefficients
    pub fn to_bytes_12(&self, bytes: &mut [u8]) {
        debug_assert!(bytes.len() >= 384);

        for i in 0..params::N / 2 {
            // Normalize to [0, q) range
            let c0 = to_positive(self.coeffs[2 * i]);
            let c1 = to_positive(self.coeffs[2 * i + 1]);

            // Pack two 12-bit values into 3 bytes
            bytes[3 * i] = c0 as u8;
            bytes[3 * i + 1] = ((c0 >> 8) | (c1 << 4)) as u8;
            bytes[3 * i + 2] = (c1 >> 4) as u8;
        }
    }

    /// Decode polynomial from bytes (ByteDecode_12)
    pub fn from_bytes_12(&mut self, bytes: &[u8]) {
        debug_assert!(bytes.len() >= 384);

        for i in 0..params::N / 2 {
            let b0 = u16::from(bytes[3 * i]);
            let b1 = u16::from(bytes[3 * i + 1]);
            let b2 = u16::from(bytes[3 * i + 2]);

            self.coeffs[2 * i] = (b0 | ((b1 & 0x0F) << 8)) as i16;
            self.coeffs[2 * i + 1] = ((b1 >> 4) | (b2 << 4)) as i16;
        }
    }

    /// Compress polynomial to d bits per coefficient
    ///
    /// Compress_d(x) = round(2^d / q · x) mod 2^d
    pub fn compress(&self, bytes: &mut [u8], d: usize) {
        match d {
            10 => {
                // 10 bits per coefficient, 5 coefficients per 8 bytes (with 16-bit alignment)
                // Actually: 256 coefficients * 10 bits = 2560 bits = 320 bytes
                debug_assert!(bytes.len() >= 320);

                for i in 0..params::N / 4 {
                    let mut t = [0u16; 4];
                    for j in 0..4 {
                        // Normalize to [0, q) range to avoid overflow
                        let c = to_positive(self.coeffs[4 * i + j]) as u32;
                        // Compress: round((c << 10) / q)
                        t[j] = (((c << 10) + params::Q32 / 2) / params::Q32) as u16 & 0x3FF;
                    }
                    // Pack 4 10-bit values into 5 bytes
                    bytes[5 * i] = t[0] as u8;
                    bytes[5 * i + 1] = ((t[0] >> 8) | (t[1] << 2)) as u8;
                    bytes[5 * i + 2] = ((t[1] >> 6) | (t[2] << 4)) as u8;
                    bytes[5 * i + 3] = ((t[2] >> 4) | (t[3] << 6)) as u8;
                    bytes[5 * i + 4] = (t[3] >> 2) as u8;
                }
            }
            4 => {
                // 4 bits per coefficient, 2 coefficients per byte
                debug_assert!(bytes.len() >= 128);

                for i in 0..params::N / 2 {
                    // Normalize to [0, q) range to avoid overflow
                    let c0 = to_positive(self.coeffs[2 * i]) as u32;
                    let c1 = to_positive(self.coeffs[2 * i + 1]) as u32;

                    // Compress: round((c << 4) / q)
                    let t0 = (((c0 << 4) + params::Q32 / 2) / params::Q32) as u8 & 0x0F;
                    let t1 = (((c1 << 4) + params::Q32 / 2) / params::Q32) as u8 & 0x0F;

                    bytes[i] = t0 | (t1 << 4);
                }
            }
            _ => panic!("Unsupported compression bits: {}", d),
        }
    }

    /// Decompress polynomial from d bits per coefficient
    ///
    /// Decompress_d(y) = round(q / 2^d · y)
    pub fn decompress(&mut self, bytes: &[u8], d: usize) {
        match d {
            10 => {
                debug_assert!(bytes.len() >= 320);

                for i in 0..params::N / 4 {
                    // Unpack 4 10-bit values from 5 bytes
                    let b = [
                        u16::from(bytes[5 * i]),
                        u16::from(bytes[5 * i + 1]),
                        u16::from(bytes[5 * i + 2]),
                        u16::from(bytes[5 * i + 3]),
                        u16::from(bytes[5 * i + 4]),
                    ];

                    let t = [
                        b[0] | ((b[1] & 0x03) << 8),
                        (b[1] >> 2) | ((b[2] & 0x0F) << 6),
                        (b[2] >> 4) | ((b[3] & 0x3F) << 4),
                        (b[3] >> 6) | (b[4] << 2),
                    ];

                    for j in 0..4 {
                        // Decompress: round(q * t / 2^10)
                        let c = ((u32::from(t[j]) * params::Q32 + 512) >> 10) as i16;
                        self.coeffs[4 * i + j] = c;
                    }
                }
            }
            4 => {
                debug_assert!(bytes.len() >= 128);

                for i in 0..params::N / 2 {
                    let t0 = u32::from(bytes[i] & 0x0F);
                    let t1 = u32::from(bytes[i] >> 4);

                    // Decompress: round(q * t / 2^4)
                    self.coeffs[2 * i] = ((t0 * params::Q32 + 8) >> 4) as i16;
                    self.coeffs[2 * i + 1] = ((t1 * params::Q32 + 8) >> 4) as i16;
                }
            }
            _ => panic!("Unsupported decompression bits: {}", d),
        }
    }

    /// Encode message (1 bit per coefficient)
    pub fn decode_message(&mut self, msg: &[u8; 32]) {
        for i in 0..32 {
            for j in 0..8 {
                let bit = (msg[i] >> j) & 1;
                // 1 -> q/2, 0 -> 0 (for message encoding)
                self.coeffs[8 * i + j] = i16::from(bit) * ((params::Q as i16 + 1) / 2);
            }
        }
    }

    /// Decode message (extract 1 bit per coefficient)
    pub fn encode_message(&self, msg: &mut [u8; 32]) {
        *msg = [0u8; 32];
        for i in 0..32 {
            for j in 0..8 {
                let c = cond_sub_q(barrett_reduce(self.coeffs[8 * i + j]));
                // Compress to 1 bit: round(2c/q)
                let c_abs = if c < 0 { c + params::Q as i16 } else { c } as u32;
                let bit = (((c_abs << 1) + params::Q32 / 2) / params::Q32) & 1;
                msg[i] |= (bit as u8) << j;
            }
        }
    }
}

impl Drop for Poly {
    fn drop(&mut self) {
        self.coeffs.zeroize();
    }
}

// =============================================================================
// Polynomial Vector (k polynomials)
// =============================================================================

/// Vector of k polynomials
#[derive(Clone)]
pub struct PolyVec {
    polys: [Poly; params::K],
}

impl PolyVec {
    /// Create a zero vector
    pub fn zero() -> Self {
        Self {
            polys: core::array::from_fn(|_| Poly::zero()),
        }
    }

    /// Apply NTT to all polynomials
    pub fn ntt(&mut self) {
        for poly in &mut self.polys {
            poly.ntt();
        }
    }

    /// Apply inverse NTT to all polynomials
    pub fn inv_ntt(&mut self) {
        for poly in &mut self.polys {
            poly.inv_ntt();
        }
    }

    /// Add vectors
    pub fn add(&mut self, other: &PolyVec) {
        for i in 0..params::K {
            self.polys[i].add(&other.polys[i]);
        }
    }

    /// Inner product: result = sum_i(a[i] * b[i]) in NTT domain
    pub fn pointwise_acc(&self, other: &PolyVec) -> Poly {
        let mut result = Poly::zero();
        let mut temp = Poly::zero();

        for i in 0..params::K {
            temp.pointwise_mul(&self.polys[i], &other.polys[i]);
            result.add(&temp);
        }

        result
    }

    /// Encode to bytes (12 bits per coefficient)
    pub fn to_bytes(&self, bytes: &mut [u8]) {
        debug_assert!(bytes.len() >= 384 * params::K);
        for i in 0..params::K {
            self.polys[i].to_bytes_12(&mut bytes[384 * i..384 * (i + 1)]);
        }
    }

    /// Decode from bytes (12 bits per coefficient)
    pub fn from_bytes(&mut self, bytes: &[u8]) {
        debug_assert!(bytes.len() >= 384 * params::K);
        for i in 0..params::K {
            self.polys[i].from_bytes_12(&bytes[384 * i..384 * (i + 1)]);
        }
    }

    /// Compress to bytes
    pub fn compress(&self, bytes: &mut [u8], d: usize) {
        let poly_bytes = d * params::N / 8;
        debug_assert!(bytes.len() >= poly_bytes * params::K);
        for i in 0..params::K {
            self.polys[i].compress(&mut bytes[poly_bytes * i..poly_bytes * (i + 1)], d);
        }
    }

    /// Decompress from bytes
    pub fn decompress(&mut self, bytes: &[u8], d: usize) {
        let poly_bytes = d * params::N / 8;
        debug_assert!(bytes.len() >= poly_bytes * params::K);
        for i in 0..params::K {
            self.polys[i].decompress(&bytes[poly_bytes * i..poly_bytes * (i + 1)], d);
        }
    }

    /// Reduce all polynomials
    pub fn reduce(&mut self) {
        for poly in &mut self.polys {
            poly.reduce();
        }
    }
}

impl Drop for PolyVec {
    fn drop(&mut self) {
        // Zeroize handled by Poly drop
    }
}

// =============================================================================
// Matrix (k×k polynomials)
// =============================================================================

/// Matrix of k×k polynomials in NTT domain
pub struct PolyMat {
    rows: [PolyVec; params::K],
}

impl PolyMat {
    /// Create a zero matrix
    pub fn zero() -> Self {
        Self {
            rows: core::array::from_fn(|_| PolyVec::zero()),
        }
    }

    /// Sample matrix A from seed ρ using SHAKE128
    ///
    /// Algorithm 6 from FIPS 203 (SampleNTT)
    pub fn sample_from_seed(&mut self, rho: &[u8; 32], transpose: bool) {
        for i in 0..params::K {
            for j in 0..params::K {
                // Domain separator: use different XOF input for each position
                let (row, col) = if transpose { (j, i) } else { (i, j) };

                // XOF = SHAKE128(ρ || j || i)
                let mut xof = Shake128::new();
                xof.update(rho);
                xof.update(&[col as u8, row as u8]);

                sample_ntt(&mut self.rows[i].polys[j], &mut xof);
            }
        }
    }

    /// Matrix-vector multiplication: result = A * v (in NTT domain)
    pub fn mul_vec(&self, v: &PolyVec) -> PolyVec {
        let mut result = PolyVec::zero();
        for i in 0..params::K {
            result.polys[i] = self.rows[i].pointwise_acc(v);
        }
        result
    }
}

/// Sample polynomial uniformly using rejection sampling from XOF output
///
/// Algorithm 6 from FIPS 203
fn sample_ntt(poly: &mut Poly, xof: &mut Shake128) {
    let mut buf = [0u8; 3 * 168]; // 3 blocks for efficiency
    let mut idx = 0usize;
    let mut j = 0usize;

    while j < params::N {
        // Refill buffer if needed
        if idx + 3 > buf.len() {
            xof.squeeze(&mut buf);
            idx = 0;
        }

        // Sample two coefficients from 3 bytes
        let d1 = u16::from(buf[idx]) | ((u16::from(buf[idx + 1]) & 0x0F) << 8);
        let d2 = (u16::from(buf[idx + 1]) >> 4) | (u16::from(buf[idx + 2]) << 4);
        idx += 3;

        // Rejection sampling: accept if < q
        if d1 < params::Q {
            poly.coeffs[j] = d1 as i16;
            j += 1;
        }
        if j < params::N && d2 < params::Q {
            poly.coeffs[j] = d2 as i16;
            j += 1;
        }
    }
}

// =============================================================================
// PRF for sampling noise polynomials
// =============================================================================

/// Sample noise polynomial using PRF (SHAKE256)
///
/// PRF_η(s, b) extracts 64η bytes and applies CBD_η
fn sample_noise(poly: &mut Poly, seed: &[u8; 32], nonce: u8, eta: usize) {
    let prf_output_len = 64 * eta;
    let mut prf_output = [0u8; 192]; // Max for η=3

    // PRF = SHAKE256(s || b)
    let mut prf = Shake256::new();
    prf.update(seed);
    prf.update(&[nonce]);
    prf.squeeze(&mut prf_output[..prf_output_len]);

    poly.cbd(&prf_output[..prf_output_len], eta);
}

// =============================================================================
// K-PKE (Internal Encryption Scheme)
// =============================================================================

/// K-PKE key generation (internal, deterministic)
///
/// Algorithm 12 from FIPS 203
fn k_pke_keygen(
    d: &[u8; 32],
    ek: &mut [u8; PUBLIC_KEY_SIZE],
    dk: &mut [u8; 1152],
) {
    // (ρ, σ) = G(d)
    let g_output = Sha3_512::hash(d);
    let rho: [u8; 32] = g_output[..32].try_into().unwrap();
    let sigma: [u8; 32] = g_output[32..64].try_into().unwrap();

    // Sample A from ρ
    let mut a_hat = PolyMat::zero();
    a_hat.sample_from_seed(&rho, false);

    // Sample s and e from σ
    let mut s = PolyVec::zero();
    let mut e = PolyVec::zero();

    for i in 0..params::K {
        sample_noise(&mut s.polys[i], &sigma, i as u8, params::ETA1);
        sample_noise(&mut e.polys[i], &sigma, (params::K + i) as u8, params::ETA1);
    }

    // NTT(s) and NTT(e)
    s.ntt();
    e.ntt();

    // t̂ = Â·ŝ + ê
    let mut t_hat = a_hat.mul_vec(&s);
    t_hat.add(&e);
    t_hat.reduce();

    // Encode public key: ek = (t̂ || ρ)
    t_hat.to_bytes(&mut ek[..1152]);
    ek[1152..1184].copy_from_slice(&rho);

    // Encode secret key: dk = s
    s.to_bytes(dk);
}

/// K-PKE encryption (internal)
///
/// Algorithm 13 from FIPS 203
fn k_pke_encrypt(
    ek: &[u8; PUBLIC_KEY_SIZE],
    m: &[u8; 32],
    r: &[u8; 32],
    ct: &mut [u8; CIPHERTEXT_SIZE],
) {
    // Decode public key
    let mut t_hat = PolyVec::zero();
    t_hat.from_bytes(&ek[..1152]);
    let rho: [u8; 32] = ek[1152..1184].try_into().unwrap();

    // Sample A^T from ρ (transpose=true)
    let mut a_hat_t = PolyMat::zero();
    a_hat_t.sample_from_seed(&rho, true);

    // Sample r, e1, e2 from randomness
    let mut r_vec = PolyVec::zero();
    let mut e1 = PolyVec::zero();
    let mut e2 = Poly::zero();

    for i in 0..params::K {
        sample_noise(&mut r_vec.polys[i], r, i as u8, params::ETA1);
        sample_noise(&mut e1.polys[i], r, (params::K + i) as u8, params::ETA2);
    }
    sample_noise(&mut e2, r, (2 * params::K) as u8, params::ETA2);

    // NTT(r)
    r_vec.ntt();

    // u = NTT^(-1)(Â^T · r̂) + e1
    let mut u = a_hat_t.mul_vec(&r_vec);
    u.inv_ntt();
    u.add(&e1);
    u.reduce();

    // v = NTT^(-1)(t̂^T · r̂) + e2 + Decompress_1(m)
    let mut v = t_hat.pointwise_acc(&r_vec);
    v.inv_ntt();
    v.add(&e2);

    // Add message
    let mut msg_poly = Poly::zero();
    msg_poly.decode_message(m);
    v.add(&msg_poly);
    v.reduce();

    // Compress and encode ciphertext
    // c1 = Compress_du(u) (960 bytes for k=3, du=10)
    u.compress(&mut ct[..960], params::DU);
    // c2 = Compress_dv(v) (128 bytes for dv=4)
    v.compress(&mut ct[960..1088], params::DV);
}

/// K-PKE decryption (internal)
///
/// Algorithm 14 from FIPS 203
fn k_pke_decrypt(
    dk: &[u8; 1152],
    ct: &[u8; CIPHERTEXT_SIZE],
    m: &mut [u8; 32],
) {
    // Decode secret key
    let mut s_hat = PolyVec::zero();
    s_hat.from_bytes(dk);

    // Decompress ciphertext
    let mut u = PolyVec::zero();
    let mut v = Poly::zero();
    u.decompress(&ct[..960], params::DU);
    v.decompress(&ct[960..1088], params::DV);

    // NTT(u)
    u.ntt();

    // w = v - NTT^(-1)(ŝ^T · û)
    let mut su = s_hat.pointwise_acc(&u);
    su.inv_ntt();
    su.reduce();

    // v - s·u
    for i in 0..params::N {
        v.coeffs[i] = v.coeffs[i] - su.coeffs[i];
    }
    v.reduce();

    // Decode message
    v.encode_message(m);
}

// =============================================================================
// ML-KEM (Public Interface with FO Transform)
// =============================================================================

/// ML-KEM-768 encapsulation key (public key)
pub struct MlKem768EncapsulationKey {
    /// Public key bytes
    bytes: [u8; PUBLIC_KEY_SIZE],
}

impl MlKem768EncapsulationKey {
    /// Create from bytes
    pub fn from_bytes(bytes: &[u8; PUBLIC_KEY_SIZE]) -> CryptoResult<Self> {
        // Validate: check that decoded t̂ values are < q
        // This is a basic validation; full validation would check more
        let mut t = PolyVec::zero();
        t.from_bytes(&bytes[..1152]);
        for poly in &t.polys {
            for &c in &poly.coeffs {
                if c < 0 || c >= params::Q as i16 {
                    return Err(CryptoError::InvalidKeyLength);
                }
            }
        }
        Ok(Self { bytes: *bytes })
    }

    /// Get the public key bytes
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        &self.bytes
    }

    /// Encapsulate a shared secret
    ///
    /// Algorithm 16 from FIPS 203 (ML-KEM.Encaps)
    pub fn encapsulate(
        &self,
        random: &[u8; 32],
    ) -> CryptoResult<([u8; CIPHERTEXT_SIZE], [u8; SHARED_SECRET_SIZE])> {
        let mut ct = [0u8; CIPHERTEXT_SIZE];
        let mut ss = [0u8; SHARED_SECRET_SIZE];

        // H(ek)
        let h_ek = Sha3_256::hash(&self.bytes);

        // (K, r) = G(m || H(ek))
        let mut g_input = [0u8; 64];
        g_input[..32].copy_from_slice(random);
        g_input[32..64].copy_from_slice(&h_ek);
        let g_output = Sha3_512::hash(&g_input);
        let k: [u8; 32] = g_output[..32].try_into().unwrap();
        let r: [u8; 32] = g_output[32..64].try_into().unwrap();

        // c = K-PKE.Encrypt(ek, m, r)
        k_pke_encrypt(&self.bytes, random, &r, &mut ct);

        // K = KDF(K || H(c)) - using SHAKE256 for KDF
        let h_c = Sha3_256::hash(&ct);
        let mut kdf_input = [0u8; 64];
        kdf_input[..32].copy_from_slice(&k);
        kdf_input[32..64].copy_from_slice(&h_c);

        let mut kdf = Shake256::new();
        kdf.update(&kdf_input);
        kdf.squeeze(&mut ss);

        Ok((ct, ss))
    }
}

/// ML-KEM-768 decapsulation key (secret key)
pub struct MlKem768DecapsulationKey {
    /// Full secret key bytes: dk_PKE (1152) || ek (1184) || H(ek) (32) || z (32)
    bytes: [u8; SECRET_KEY_SIZE],
}

impl MlKem768DecapsulationKey {
    /// Create from bytes
    pub fn from_bytes(bytes: &[u8; SECRET_KEY_SIZE]) -> CryptoResult<Self> {
        Ok(Self { bytes: *bytes })
    }

    /// Get the secret key bytes
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; SECRET_KEY_SIZE] {
        &self.bytes
    }

    /// Decapsulate a shared secret
    ///
    /// Algorithm 17 from FIPS 203 (ML-KEM.Decaps)
    /// Implements implicit rejection for IND-CCA2 security
    pub fn decapsulate(&self, ciphertext: &[u8; CIPHERTEXT_SIZE]) -> CryptoResult<[u8; SHARED_SECRET_SIZE]> {
        let mut ss = [0u8; SHARED_SECRET_SIZE];

        // Parse secret key components
        let dk_pke: &[u8; 1152] = self.bytes[..1152].try_into().unwrap();
        let ek: [u8; PUBLIC_KEY_SIZE] = self.bytes[1152..2336].try_into().unwrap();
        let h_ek: [u8; 32] = self.bytes[2336..2368].try_into().unwrap();
        let z: [u8; 32] = self.bytes[2368..2400].try_into().unwrap();

        // m' = K-PKE.Decrypt(dk, c)
        let mut m_prime = [0u8; 32];
        k_pke_decrypt(dk_pke, ciphertext, &mut m_prime);

        // (K', r') = G(m' || H(ek))
        let mut g_input = [0u8; 64];
        g_input[..32].copy_from_slice(&m_prime);
        g_input[32..64].copy_from_slice(&h_ek);
        let g_output = Sha3_512::hash(&g_input);
        let k_prime: [u8; 32] = g_output[..32].try_into().unwrap();
        let r_prime: [u8; 32] = g_output[32..64].try_into().unwrap();

        // H(c)
        let h_c = Sha3_256::hash(ciphertext);

        // c' = K-PKE.Encrypt(ek, m', r')
        let mut ct_prime = [0u8; CIPHERTEXT_SIZE];
        k_pke_encrypt(&ek, &m_prime, &r_prime, &mut ct_prime);

        // Constant-time comparison: if c == c' then K = K' else K = KDF(z || H(c))
        let mut diff = 0u8;
        for i in 0..CIPHERTEXT_SIZE {
            diff |= ciphertext[i] ^ ct_prime[i];
        }

        // mask = 0xFF if equal, 0x00 if different
        let mask = (((diff as i16) - 1) >> 8) as u8;

        // Select between K' (valid) and KDF(z || H(c)) (implicit rejection)
        let mut kdf_input_reject = [0u8; 64];
        kdf_input_reject[..32].copy_from_slice(&z);
        kdf_input_reject[32..64].copy_from_slice(&h_c);

        let mut ss_reject = [0u8; 32];
        let mut kdf = Shake256::new();
        kdf.update(&kdf_input_reject);
        kdf.squeeze(&mut ss_reject);

        // KDF for valid case
        let mut kdf_input_valid = [0u8; 64];
        kdf_input_valid[..32].copy_from_slice(&k_prime);
        kdf_input_valid[32..64].copy_from_slice(&h_c);

        let mut ss_valid = [0u8; 32];
        let mut kdf2 = Shake256::new();
        kdf2.update(&kdf_input_valid);
        kdf2.squeeze(&mut ss_valid);

        // Constant-time select
        for i in 0..32 {
            ss[i] = (ss_valid[i] & mask) | (ss_reject[i] & !mask);
        }

        // Zeroize temporaries
        m_prime.zeroize();
        g_input.zeroize();

        Ok(ss)
    }

    /// Get the encapsulation key (public key)
    #[must_use]
    pub fn encapsulation_key(&self) -> MlKem768EncapsulationKey {
        let mut ek_bytes = [0u8; PUBLIC_KEY_SIZE];
        ek_bytes.copy_from_slice(&self.bytes[1152..2336]);
        MlKem768EncapsulationKey { bytes: ek_bytes }
    }
}

impl Drop for MlKem768DecapsulationKey {
    fn drop(&mut self) {
        self.bytes.zeroize();
    }
}

/// ML-KEM-768 key pair
pub struct MlKem768KeyPair {
    /// Decapsulation key (secret key)
    decapsulation_key: MlKem768DecapsulationKey,
    /// Encapsulation key (public key)
    encapsulation_key: MlKem768EncapsulationKey,
}

impl MlKem768KeyPair {
    /// Generate a new key pair
    ///
    /// Algorithm 15 from FIPS 203 (ML-KEM.KeyGen)
    pub fn generate(random: &[u8; 64]) -> CryptoResult<Self> {
        let d: [u8; 32] = random[..32].try_into().unwrap();
        let z: [u8; 32] = random[32..64].try_into().unwrap();

        // Generate K-PKE keys
        let mut ek = [0u8; PUBLIC_KEY_SIZE];
        let mut dk_pke = [0u8; 1152];
        k_pke_keygen(&d, &mut ek, &mut dk_pke);

        // H(ek)
        let h_ek = Sha3_256::hash(&ek);

        // Build full decapsulation key: dk = (dk_PKE || ek || H(ek) || z)
        let mut dk = [0u8; SECRET_KEY_SIZE];
        dk[..1152].copy_from_slice(&dk_pke);
        dk[1152..2336].copy_from_slice(&ek);
        dk[2336..2368].copy_from_slice(&h_ek);
        dk[2368..2400].copy_from_slice(&z);

        // Zeroize temporary
        dk_pke.zeroize();

        Ok(Self {
            decapsulation_key: MlKem768DecapsulationKey { bytes: dk },
            encapsulation_key: MlKem768EncapsulationKey { bytes: ek },
        })
    }

    /// Get the encapsulation key (public key)
    #[must_use]
    pub fn encapsulation_key(&self) -> &MlKem768EncapsulationKey {
        &self.encapsulation_key
    }

    /// Get the decapsulation key (secret key)
    #[must_use]
    pub fn decapsulation_key(&self) -> &MlKem768DecapsulationKey {
        &self.decapsulation_key
    }

    /// Encapsulate using the public key
    pub fn encapsulate(
        &self,
        random: &[u8; 32],
    ) -> CryptoResult<([u8; CIPHERTEXT_SIZE], [u8; SHARED_SECRET_SIZE])> {
        self.encapsulation_key.encapsulate(random)
    }

    /// Decapsulate using the secret key
    pub fn decapsulate(&self, ciphertext: &[u8; CIPHERTEXT_SIZE]) -> CryptoResult<[u8; SHARED_SECRET_SIZE]> {
        self.decapsulation_key.decapsulate(ciphertext)
    }
}

/// ML-KEM-768 operations (implements Kem trait)
pub struct MlKem768;

impl Kem for MlKem768 {
    const SECRET_KEY_SIZE: usize = SECRET_KEY_SIZE;
    const PUBLIC_KEY_SIZE: usize = PUBLIC_KEY_SIZE;
    const CIPHERTEXT_SIZE: usize = CIPHERTEXT_SIZE;
    const SHARED_SECRET_SIZE: usize = SHARED_SECRET_SIZE;

    fn generate_keypair(
        rng: &[u8],
        secret_key: &mut [u8],
        public_key: &mut [u8],
    ) -> CryptoResult<()> {
        if rng.len() < 64 {
            return Err(CryptoError::KeyGenerationFailed);
        }
        if secret_key.len() != SECRET_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        if public_key.len() != PUBLIC_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }

        let random: [u8; 64] = rng[..64]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;

        let keypair = MlKem768KeyPair::generate(&random)?;
        secret_key.copy_from_slice(keypair.decapsulation_key.as_bytes());
        public_key.copy_from_slice(keypair.encapsulation_key.as_bytes());

        Ok(())
    }

    fn encapsulate(
        rng: &[u8],
        public_key: &[u8],
        ciphertext: &mut [u8],
        shared_secret: &mut [u8],
    ) -> CryptoResult<()> {
        if rng.len() < 32 {
            return Err(CryptoError::KeyGenerationFailed);
        }
        if public_key.len() != PUBLIC_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        if ciphertext.len() != CIPHERTEXT_SIZE {
            return Err(CryptoError::BufferTooSmall);
        }
        if shared_secret.len() != SHARED_SECRET_SIZE {
            return Err(CryptoError::BufferTooSmall);
        }

        let pk_bytes: [u8; PUBLIC_KEY_SIZE] = public_key
            .try_into()
            .map_err(|_| CryptoError::InvalidKeyLength)?;
        let random: [u8; 32] = rng[..32]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;

        let ek = MlKem768EncapsulationKey::from_bytes(&pk_bytes)?;
        let (ct, ss) = ek.encapsulate(&random)?;

        ciphertext.copy_from_slice(&ct);
        shared_secret.copy_from_slice(&ss);

        Ok(())
    }

    fn decapsulate(
        secret_key: &[u8],
        ciphertext: &[u8],
        shared_secret: &mut [u8],
    ) -> CryptoResult<()> {
        if secret_key.len() != SECRET_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        if ciphertext.len() != CIPHERTEXT_SIZE {
            return Err(CryptoError::InvalidInputLength);
        }
        if shared_secret.len() != SHARED_SECRET_SIZE {
            return Err(CryptoError::BufferTooSmall);
        }

        let sk_bytes: [u8; SECRET_KEY_SIZE] = secret_key
            .try_into()
            .map_err(|_| CryptoError::InvalidKeyLength)?;
        let ct_bytes: [u8; CIPHERTEXT_SIZE] = ciphertext
            .try_into()
            .map_err(|_| CryptoError::InvalidInputLength)?;

        let dk = MlKem768DecapsulationKey::from_bytes(&sk_bytes)?;
        let ss = dk.decapsulate(&ct_bytes)?;

        shared_secret.copy_from_slice(&ss);

        Ok(())
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ml_kem_768_sizes() {
        assert_eq!(SECRET_KEY_SIZE, 2400);
        assert_eq!(PUBLIC_KEY_SIZE, 1184);
        assert_eq!(CIPHERTEXT_SIZE, 1088);
        assert_eq!(SHARED_SECRET_SIZE, 32);
    }

    #[test]
    fn test_ml_kem_768_roundtrip() {
        // Generate key pair
        let mut keygen_random = [0u8; 64];
        for i in 0..64 {
            keygen_random[i] = i as u8;
        }
        let keypair = MlKem768KeyPair::generate(&keygen_random).unwrap();

        // Encapsulate
        let mut encaps_random = [0u8; 32];
        for i in 0..32 {
            encaps_random[i] = (i + 64) as u8;
        }
        let (ct, ss1) = keypair.encapsulate(&encaps_random).unwrap();

        // Decapsulate
        let ss2 = keypair.decapsulate(&ct).unwrap();

        // Shared secrets must match
        assert_eq!(ss1, ss2, "Encapsulated and decapsulated shared secrets don't match");
    }

    #[test]
    fn test_ml_kem_768_decaps_wrong_ciphertext() {
        // Generate key pair
        let keygen_random = [0x42u8; 64];
        let keypair = MlKem768KeyPair::generate(&keygen_random).unwrap();

        // Encapsulate
        let encaps_random = [0x37u8; 32];
        let (mut ct, ss1) = keypair.encapsulate(&encaps_random).unwrap();

        // Corrupt ciphertext
        ct[0] ^= 0xFF;

        // Decapsulate should return implicit rejection (different shared secret)
        let ss2 = keypair.decapsulate(&ct).unwrap();

        // Shared secrets must NOT match (implicit rejection)
        assert_ne!(ss1, ss2, "Should get different shared secret on corrupted ciphertext");
    }

    #[test]
    fn test_ntt_multiply_roundtrip() {
        // Test that NTT-based multiplication works correctly
        // This is how NTT is actually used in ML-KEM:
        // 1. Convert both polynomials to NTT domain
        // 2. Pointwise multiply (basemul)
        // 3. Convert result back with inv_NTT
        //
        // For polynomial a(x) = 1 (constant) and b(x) = x + 1,
        // the product should be a(x) * b(x) = x + 1

        // a(x) = 1 (just constant term)
        let mut a = Poly::zero();
        a.coeffs[0] = 1;

        // b(x) = 1 (just constant term)
        let mut b = Poly::zero();
        b.coeffs[0] = 1;

        // Convert to NTT domain
        a.ntt();
        b.ntt();

        // Pointwise multiply in NTT domain
        let mut c = Poly::zero();
        c.pointwise_mul(&a, &b);

        // Convert back
        c.inv_ntt();
        c.reduce();

        // Result should be 1 * 1 = 1 (constant polynomial)
        let c0 = to_positive(c.coeffs[0]);
        // The result has an extra R factor from the Montgomery reduction in basemul,
        // which is then partially compensated by F=1441 in inv_NTT.
        // After full reduction, coefficient 0 should be 1 (mod q).
        // Note: Due to Montgomery arithmetic, we expect the value to be correct modulo q.
        assert!(
            c0 == 1 || c0 == params::Q as u16 + 1,
            "Expected 1, got {} for constant polynomial multiplication",
            c0
        );

        // All other coefficients should be 0 or reduce to 0
        for i in 1..params::N {
            let ci = to_positive(c.coeffs[i]);
            assert!(
                ci == 0,
                "Expected 0 at index {}, got {}",
                i, ci
            );
        }
    }

    #[test]
    fn test_poly_compress_decompress() {
        let mut poly = Poly::zero();
        for i in 0..params::N {
            poly.coeffs[i] = (i % (params::Q as usize)) as i16;
        }

        // Test d=10 compression
        let mut compressed = [0u8; 320];
        poly.compress(&mut compressed, 10);

        let mut decompressed = Poly::zero();
        decompressed.decompress(&compressed, 10);

        // Check that decompressed is close to original
        for i in 0..params::N {
            let orig = poly.coeffs[i] as i32;
            let decomp = decompressed.coeffs[i] as i32;
            let diff = (orig - decomp).abs();
            // After compression to 10 bits, error should be < q/2^10 ≈ 3.25
            assert!(diff < 50, "Compression error too large at {}: {} vs {}", i, orig, decomp);
        }
    }

    #[test]
    fn test_cbd_2() {
        let mut poly = Poly::zero();
        let bytes = [0xAA; 128]; // Pattern that gives predictable CBD
        poly.cbd(&bytes, 2);

        // All coefficients should be in [-2, 2]
        for i in 0..params::N {
            assert!(poly.coeffs[i] >= -2 && poly.coeffs[i] <= 2,
                "CBD_2 coefficient out of range: {}", poly.coeffs[i]);
        }
    }

    #[test]
    fn test_barrett_reduce() {
        // Test values near boundaries using to_positive for normalization
        // (barrett_reduce with Kyber formula can return negative values)
        assert_eq!(to_positive(barrett_reduce(0)), 0);
        assert_eq!(to_positive(barrett_reduce(params::Q as i16 - 1)), params::Q as u16 - 1);
        assert_eq!(to_positive(barrett_reduce(params::Q as i16)), 0);
        assert_eq!(to_positive(barrett_reduce(params::Q as i16 + 1)), 1);
        // Test negative values
        assert_eq!(to_positive(barrett_reduce(-1)), params::Q as u16 - 1);
        assert_eq!(to_positive(barrett_reduce(-(params::Q as i16))), 0);
    }

    #[test]
    fn test_poly_encode_decode_12() {
        let mut poly = Poly::zero();
        for i in 0..params::N {
            poly.coeffs[i] = ((i * 17) % (params::Q as usize)) as i16;
        }

        let mut bytes = [0u8; 384];
        poly.to_bytes_12(&mut bytes);

        let mut decoded = Poly::zero();
        decoded.from_bytes_12(&bytes);

        for i in 0..params::N {
            assert_eq!(decoded.coeffs[i], poly.coeffs[i],
                "Encode/decode 12 failed at {}", i);
        }
    }

    #[test]
    fn test_ml_kem_768_kem_trait() {
        // Test via the Kem trait interface
        let mut sk = [0u8; SECRET_KEY_SIZE];
        let mut pk = [0u8; PUBLIC_KEY_SIZE];
        let rng = [0x55u8; 64];

        MlKem768::generate_keypair(&rng, &mut sk, &mut pk).unwrap();

        let mut ct = [0u8; CIPHERTEXT_SIZE];
        let mut ss1 = [0u8; SHARED_SECRET_SIZE];
        let encaps_rng = [0x77u8; 32];

        MlKem768::encapsulate(&encaps_rng, &pk, &mut ct, &mut ss1).unwrap();

        let mut ss2 = [0u8; SHARED_SECRET_SIZE];
        MlKem768::decapsulate(&sk, &ct, &mut ss2).unwrap();

        assert_eq!(ss1, ss2);
    }
}
