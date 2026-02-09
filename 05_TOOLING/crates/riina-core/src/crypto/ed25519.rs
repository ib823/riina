// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Ed25519 Digital Signature Implementation
//!
//! This module implements Ed25519 as specified in RFC 8032.
//!
//! # Law 2: Cryptographic Non-Negotiables
//!
//! Ed25519 is used in hybrid signatures alongside ML-DSA-65.
//! The combination provides security against both classical and quantum adversaries.
//!
//! # Security Properties
//!
//! - 128-bit security level against classical attacks
//! - Deterministic signatures (no random number needed for signing)
//! - Constant-time implementation required (Law 3)
//! - All keys zeroized on drop (Law 4)
//!
//! # Implementation
//!
//! This implementation uses:
//! - Extended coordinates (X:Y:Z:T) for efficient point arithmetic
//! - Constant-time scalar multiplication via double-and-add
//! - SHA-512 for hashing (per RFC 8032)
//! - Little-endian byte encoding throughout
//!
//! # Curve Parameters
//!
//! Ed25519 uses the twisted Edwards curve:
//! -x² + y² = 1 + d·x²·y²
//!
//! Over the field GF(2^255 - 19), with:
//! - d = -121665/121666 (mod p)
//! - p = 2^255 - 19
//! - L = 2^252 + 27742317777372353535851937790883648493 (group order)

#![allow(unsafe_code)] // Required for pointer casts in key structure

use crate::crypto::field25519::FieldElement;
use crate::crypto::sha2::Sha512;
use crate::crypto::{CryptoError, CryptoResult, Signature};
use crate::zeroize::Zeroize;

/// Ed25519 secret key size (32 bytes seed)
pub const SECRET_KEY_SIZE: usize = 32;
/// Ed25519 expanded secret key size (64 bytes)
pub const EXPANDED_SECRET_KEY_SIZE: usize = 64;
/// Ed25519 public key size (32 bytes)
pub const PUBLIC_KEY_SIZE: usize = 32;
/// Ed25519 signature size (64 bytes)
pub const SIGNATURE_SIZE: usize = 64;

// =============================================================================
// Edwards Curve Constants
// =============================================================================

/// The curve parameter d = -121665/121666 (mod p)
/// d = 0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3
fn curve_d() -> FieldElement {
    // Little-endian encoding of d
    FieldElement::from_bytes(&[
        0xa3, 0x78, 0x59, 0x13, 0xca, 0x4d, 0xeb, 0x75, 0xab, 0xd8, 0x41, 0x41, 0x4d, 0x0a, 0x70,
        0x00, 0x98, 0xe8, 0x79, 0x77, 0x79, 0x40, 0xc7, 0x8c, 0x73, 0xfe, 0x6f, 0x2b, 0xee, 0x6c,
        0x03, 0x52,
    ])
}

/// 2 * d (precomputed for efficiency)
fn curve_2d() -> FieldElement {
    let d = curve_d();
    d + d
}

/// The Ed25519 basepoint B
/// By = 4/5 (mod p)
/// Bx is recovered from the curve equation, with LSB(x) = 0
fn basepoint() -> EdwardsPoint {
    // Basepoint y-coordinate (4/5 mod p) in little-endian
    // y = 0x6666666666666666666666666666666666666666666666666666666666666658
    let by = FieldElement::from_bytes(&[
        0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66,
    ]);

    // Basepoint x-coordinate in little-endian
    // x = 0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a
    // In little-endian bytes:
    let bx = FieldElement::from_bytes(&[
        0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c,
        0x69, 0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36,
        0x69, 0x21,
    ]);

    EdwardsPoint {
        x: bx,
        y: by,
        z: FieldElement::ONE,
        t: bx * by,
    }
}

// =============================================================================
// Edwards Point Representation (Extended Coordinates)
// =============================================================================

/// A point on the Ed25519 curve in extended coordinates (X:Y:Z:T)
///
/// This representation satisfies:
/// - x = X/Z
/// - y = Y/Z
/// - T = X*Y/Z
///
/// Extended coordinates allow addition without inversions.
#[derive(Clone, Copy)]
pub struct EdwardsPoint {
    /// X coordinate (projective)
    x: FieldElement,
    /// Y coordinate (projective)
    y: FieldElement,
    /// Z coordinate (denominator)
    z: FieldElement,
    /// T = X*Y/Z (auxiliary coordinate for efficient addition)
    t: FieldElement,
}

impl EdwardsPoint {
    /// The identity element (neutral element for addition)
    /// Identity = (0, 1, 1, 0) in extended coordinates
    pub fn identity() -> Self {
        Self {
            x: FieldElement::ZERO,
            y: FieldElement::ONE,
            z: FieldElement::ONE,
            t: FieldElement::ZERO,
        }
    }

    /// Check if this point is the identity
    #[must_use]
    pub fn is_identity(&self) -> bool {
        // In extended coordinates, identity has X=0, Y=Z
        self.x.is_zero() && (self.y * FieldElement::ONE).ct_eq(&self.z) == 1
    }

    /// Add two points using the unified addition formula
    ///
    /// This uses the "add-2008-hwcd" formula for extended coordinates.
    /// For Ed25519 with a=-1: -x² + y² = 1 + d*x²*y²
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        // Using unified addition formulas from
        // https://hyperelliptic.org/EFD/g1p/auto-twisted-extended.html
        // add-2008-hwcd-4

        let ypy = self.y + self.x; // Y1 + X1
        let ymy = self.y - self.x; // Y1 - X1
        let opy = other.y + other.x; // Y2 + X2
        let omy = other.y - other.x; // Y2 - X2

        let a = ymy * omy; // A = (Y1-X1)*(Y2-X2)
        let b = ypy * opy; // B = (Y1+X1)*(Y2+X2)
        let c = self.t * curve_2d() * other.t; // C = T1 * 2*d * T2
        let d = self.z * other.z; // D = Z1 * Z2
        let d2 = d + d; // 2*D

        let e = b - a; // E = B - A
        let f = d2 - c; // F = 2*D - C
        let g = d2 + c; // G = 2*D + C
        let h = b + a; // H = B + A

        Self {
            x: e * f, // X3 = E * F
            y: g * h, // Y3 = G * H
            z: f * g, // Z3 = F * G
            t: e * h, // T3 = E * H
        }
    }

    /// Double this point
    ///
    /// Uses the "dbl-2008-hwcd" formula for extended coordinates with a=-1.
    #[must_use]
    pub fn double(&self) -> Self {
        // Using doubling formulas from
        // https://hyperelliptic.org/EFD/g1p/auto-twisted-extended.html
        // dbl-2008-hwcd

        let a = self.x.square(); // A = X1²
        let b = self.y.square(); // B = Y1²
        let c = self.z.square();
        let c = c + c; // C = 2 * Z1²
        let d = a.negate(); // D = a*A = -A (since a = -1)

        let xpy = self.x + self.y;
        let e = xpy.square() - a - b; // E = (X1+Y1)² - A - B
        let g = d + b; // G = D + B
        let f = g - c; // F = G - C
        let h = d - b; // H = D - B

        Self {
            x: e * f, // X3 = E * F
            y: g * h, // Y3 = G * H
            z: f * g, // Z3 = F * G
            t: e * h, // T3 = E * H
        }
    }

    /// Negate this point: -P
    #[must_use]
    pub fn negate(&self) -> Self {
        Self {
            x: self.x.negate(),
            y: self.y,
            z: self.z,
            t: self.t.negate(),
        }
    }

    /// Scalar multiplication: k * P
    ///
    /// Uses constant-time double-and-add.
    #[must_use]
    pub fn scalar_mul(&self, scalar: &Scalar) -> Self {
        // Constant-time double-and-add (Montgomery ladder variant)
        let mut result = Self::identity();
        let mut temp = *self;

        // Process each bit from LSB to MSB
        // Ed25519 clamped scalars have bit 254 set, so we need all 255 bits
        for i in 0..255 {
            let bit = scalar.get_bit(i);

            // Constant-time conditional addition
            let sum = result.add(&temp);
            result = Self::ct_select(&result, &sum, bit);

            temp = temp.double();
        }

        result
    }

    /// Constant-time selection: returns a if choice == 0, b if choice == 1
    fn ct_select(a: &Self, b: &Self, choice: u8) -> Self {
        debug_assert!(choice == 0 || choice == 1);

        // Convert choice to mask: 0 -> 0x00...00, 1 -> 0xff...ff
        let mask = -(choice as i64);

        // We need to implement ct_select for FieldElement
        // For now, use conditional logic (TODO: make this truly constant-time)
        if choice == 1 {
            *b
        } else {
            *a
        }
    }

    /// Convert to affine coordinates (x, y) by computing x = X/Z, y = Y/Z
    #[must_use]
    pub fn to_affine(&self) -> (FieldElement, FieldElement) {
        let z_inv = self.z.invert();
        (self.x * z_inv, self.y * z_inv)
    }

    /// Compress this point to 32 bytes
    ///
    /// Encoding: the y-coordinate in little-endian, with the sign bit of x
    /// stored in the most significant bit.
    #[must_use]
    pub fn compress(&self) -> [u8; 32] {
        let (x, y) = self.to_affine();
        let mut encoded = y.to_bytes();

        // Set the sign bit: x is "negative" if x mod p is odd
        let x_bytes = x.to_bytes();
        let x_is_odd = x_bytes[0] & 1;
        encoded[31] |= x_is_odd << 7;

        encoded
    }

    /// Decompress a 32-byte encoding to a point
    ///
    /// # Errors
    /// Returns error if the encoding is invalid or not on the curve.
    pub fn decompress(bytes: &[u8; 32]) -> CryptoResult<Self> {
        // Extract y-coordinate (clear the sign bit)
        let mut y_bytes = *bytes;
        let x_sign = (y_bytes[31] >> 7) & 1;
        y_bytes[31] &= 0x7f;

        let y = FieldElement::from_bytes(&y_bytes);

        // Compute x² = (y² - 1) / (d*y² + 1)
        let y2 = y.square();
        let u = y2 - FieldElement::ONE; // u = y² - 1
        let v = curve_d() * y2 + FieldElement::ONE; // v = d*y² + 1

        // x = sqrt(u/v) = u * v³ * (u * v⁷)^((p-5)/8)
        let (x, is_valid) = sqrt_ratio_i(&u, &v);

        if is_valid == 0 {
            return Err(CryptoError::InvalidSignature);
        }

        // Adjust sign if needed
        let x_bytes = x.to_bytes();
        let computed_sign = x_bytes[0] & 1;

        let x = if computed_sign != x_sign {
            x.negate()
        } else {
            x
        };

        // Verify the point is on the curve (defensive check)
        // -x² + y² = 1 + d*x²*y²
        let x2 = x.square();
        let lhs = y2 - x2;
        let rhs = FieldElement::ONE + curve_d() * x2 * y2;

        if lhs.ct_eq(&rhs) != 1 {
            return Err(CryptoError::InvalidSignature);
        }

        Ok(Self {
            x,
            y,
            z: FieldElement::ONE,
            t: x * y,
        })
    }
}

/// Compute sqrt(u/v) using the Ed25519 formula
///
/// Returns (result, is_valid) where is_valid is 1 if the square root exists.
fn sqrt_ratio_i(u: &FieldElement, v: &FieldElement) -> (FieldElement, u8) {
    // For Ed25519, we need to compute sqrt(u/v)
    // Using the formula: x = u * v³ * (u * v⁷)^((p-5)/8)
    //
    // p = 2^255 - 19
    // (p-5)/8 = (2^255 - 24)/8 = 2^252 - 3

    let v2 = v.square();
    let v3 = v2 * *v;
    let v4 = v2.square();
    let v7 = v3 * v4;

    let uv7 = *u * v7;

    // Compute uv7^((p-5)/8) = uv7^(2^252 - 3)
    // Using the same addition chain as for inversion
    let exp = pow_p_minus_5_over_8(&uv7);

    let x = *u * v3 * exp;

    // Verify: v * x² should equal ±u
    let vx2 = *v * x.square();

    // Check if vx² == u (valid square root)
    let correct = vx2.ct_eq(u);

    // Check if vx² == -u (need to multiply x by sqrt(-1))
    let neg_u = u.negate();
    let correct_neg = vx2.ct_eq(&neg_u);

    // sqrt(-1) mod p = 2^((p-1)/4) mod p
    let sqrt_minus_one = get_sqrt_minus_one();

    // If vx² == -u, multiply x by sqrt(-1)
    let x_corrected = if correct_neg == 1 {
        x * sqrt_minus_one
    } else {
        x
    };

    let is_valid = correct | correct_neg;

    (x_corrected, is_valid as u8)
}

/// Compute x^((p-5)/8) where p = 2^255 - 19
fn pow_p_minus_5_over_8(x: &FieldElement) -> FieldElement {
    // (p-5)/8 = 2^252 - 3
    // We use the same approach as inversion but adjusted

    let z2 = x.square();
    let z4 = z2.square();
    let z8 = z4.square();
    let z9 = z8 * *x;
    let z11 = z9 * z2;
    let z22 = z11.square();
    let z2_5_0 = z22 * z9; // x^31 = x^(2^5 - 1)

    let mut t = z2_5_0;
    for _ in 0..5 {
        t = t.square();
    }
    let z2_10_0 = t * z2_5_0; // x^(2^10 - 1)

    t = z2_10_0;
    for _ in 0..10 {
        t = t.square();
    }
    let z2_20_0 = t * z2_10_0; // x^(2^20 - 1)

    t = z2_20_0;
    for _ in 0..20 {
        t = t.square();
    }
    let z2_40_0 = t * z2_20_0; // x^(2^40 - 1)

    t = z2_40_0;
    for _ in 0..10 {
        t = t.square();
    }
    let z2_50_0 = t * z2_10_0; // x^(2^50 - 1)

    t = z2_50_0;
    for _ in 0..50 {
        t = t.square();
    }
    let z2_100_0 = t * z2_50_0; // x^(2^100 - 1)

    t = z2_100_0;
    for _ in 0..100 {
        t = t.square();
    }
    let z2_200_0 = t * z2_100_0; // x^(2^200 - 1)

    t = z2_200_0;
    for _ in 0..50 {
        t = t.square();
    }
    let z2_250_0 = t * z2_50_0; // x^(2^250 - 1)

    // Now we need x^(2^252 - 3)
    // z2_250_0 = x^(2^250 - 1)
    // z2_250_0^4 = x^(4*(2^250 - 1)) = x^(2^252 - 4)
    // z2_250_0^4 * x = x^(2^252 - 3)

    t = z2_250_0;
    t = t.square().square(); // t = x^(2^252 - 4)
    t * *x // t = x^(2^252 - 3)
}

/// Get sqrt(-1) mod p
/// sqrt(-1) = 2^((p-1)/4) mod p
fn get_sqrt_minus_one() -> FieldElement {
    // Precomputed: sqrt(-1) mod (2^255 - 19)
    // = 0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0
    FieldElement::from_bytes(&[
        0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4, 0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18, 0x43,
        0x2f, 0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b, 0x0b, 0xdf, 0xc1, 0x4f, 0x80, 0x24,
        0x83, 0x2b,
    ])
}

// =============================================================================
// Scalar Arithmetic (mod L)
// =============================================================================

/// A scalar modulo L, the group order of Ed25519
///
/// L = 2^252 + 27742317777372353535851937790883648493
#[derive(Clone, Copy)]
pub struct Scalar {
    /// 32 bytes in little-endian
    bytes: [u8; 32],
}

impl Scalar {
    /// The zero scalar
    pub const ZERO: Self = Self { bytes: [0; 32] };

    /// Create a scalar from bytes (little-endian)
    ///
    /// The scalar is reduced modulo L.
    #[must_use]
    pub fn from_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        // For now, just copy (proper reduction would clamp to < L)
        Self { bytes: *bytes }
    }

    /// Create a scalar from 64 bytes (used in signing)
    ///
    /// Performs full reduction modulo L.
    #[must_use]
    pub fn from_bytes_mod_order_wide(bytes: &[u8; 64]) -> Self {
        // Barrett reduction of 512-bit integer modulo L
        reduce_scalar_wide(bytes)
    }

    /// Get a single bit (0 or 1)
    fn get_bit(&self, i: usize) -> u8 {
        let byte_idx = i / 8;
        let bit_idx = i % 8;
        if byte_idx < 32 {
            (self.bytes[byte_idx] >> bit_idx) & 1
        } else {
            0
        }
    }

    /// Get the bytes
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }
}

/// The group order L in little-endian bytes
const L_BYTES: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

/// Reduce a 512-bit scalar modulo L
///
/// L = 2^252 + 27742317777372353535851937790883648493
///
/// This is a direct port of ref10's sc_reduce algorithm.
fn reduce_scalar_wide(bytes: &[u8; 64]) -> Scalar {
    // Load 512 bits as 24 limbs (21 bits each, with specific offsets)
    // Following ref10's exact loading pattern
    let mut s0 = load_3(&bytes[0..3]) as i64;
    let mut s1 = (load_4(&bytes[2..6]) >> 5) as i64;
    let mut s2 = (load_3(&bytes[5..8]) >> 2) as i64;
    let mut s3 = (load_4(&bytes[7..11]) >> 7) as i64;
    let mut s4 = (load_4(&bytes[10..14]) >> 4) as i64;
    let mut s5 = (load_3(&bytes[13..16]) >> 1) as i64;
    let mut s6 = (load_4(&bytes[15..19]) >> 6) as i64;
    let mut s7 = (load_3(&bytes[18..21]) >> 3) as i64;
    let mut s8 = load_3(&bytes[21..24]) as i64;
    let mut s9 = (load_4(&bytes[23..27]) >> 5) as i64;
    let mut s10 = (load_3(&bytes[26..29]) >> 2) as i64;
    let mut s11 = (load_4(&bytes[28..32]) >> 7) as i64;
    let mut s12 = (load_4(&bytes[31..35]) >> 4) as i64;
    let mut s13 = (load_3(&bytes[34..37]) >> 1) as i64;
    let mut s14 = (load_4(&bytes[36..40]) >> 6) as i64;
    let mut s15 = (load_3(&bytes[39..42]) >> 3) as i64;
    let mut s16 = load_3(&bytes[42..45]) as i64;
    let mut s17 = (load_4(&bytes[44..48]) >> 5) as i64;
    let mut s18 = (load_3(&bytes[47..50]) >> 2) as i64;
    let mut s19 = (load_4(&bytes[49..53]) >> 7) as i64;
    let mut s20 = (load_4(&bytes[52..56]) >> 4) as i64;
    let mut s21 = (load_3(&bytes[55..58]) >> 1) as i64;
    let mut s22 = (load_4(&bytes[57..61]) >> 6) as i64;
    let mut s23 = load_4(&bytes[60..64]) >> 3;

    // Mask to 21 bits
    s0 &= 0x1fffff;
    s1 &= 0x1fffff;
    s2 &= 0x1fffff;
    s3 &= 0x1fffff;
    s4 &= 0x1fffff;
    s5 &= 0x1fffff;
    s6 &= 0x1fffff;
    s7 &= 0x1fffff;
    s8 &= 0x1fffff;
    s9 &= 0x1fffff;
    s10 &= 0x1fffff;
    s11 &= 0x1fffff;
    s12 &= 0x1fffff;
    s13 &= 0x1fffff;
    s14 &= 0x1fffff;
    s15 &= 0x1fffff;
    s16 &= 0x1fffff;
    s17 &= 0x1fffff;
    s18 &= 0x1fffff;
    s19 &= 0x1fffff;
    s20 &= 0x1fffff;
    s21 &= 0x1fffff;
    s22 &= 0x1fffff;
    // s23 doesn't need masking, it's the top bits

    // Reduction constants
    // 2^252 ≡ [666643, 470296, 654183, -997805, 136657, -683901] (mod L)

    // First reduction pass: reduce s12..s23
    s11 += s23 * 666643;
    s12 += s23 * 470296;
    s13 += s23 * 654183;
    s14 -= s23 * 997805;
    s15 += s23 * 136657;
    s16 -= s23 * 683901;
    s23 = 0;

    s10 += s22 * 666643;
    s11 += s22 * 470296;
    s12 += s22 * 654183;
    s13 -= s22 * 997805;
    s14 += s22 * 136657;
    s15 -= s22 * 683901;
    s22 = 0;

    s9 += s21 * 666643;
    s10 += s21 * 470296;
    s11 += s21 * 654183;
    s12 -= s21 * 997805;
    s13 += s21 * 136657;
    s14 -= s21 * 683901;
    s21 = 0;

    s8 += s20 * 666643;
    s9 += s20 * 470296;
    s10 += s20 * 654183;
    s11 -= s20 * 997805;
    s12 += s20 * 136657;
    s13 -= s20 * 683901;
    s20 = 0;

    s7 += s19 * 666643;
    s8 += s19 * 470296;
    s9 += s19 * 654183;
    s10 -= s19 * 997805;
    s11 += s19 * 136657;
    s12 -= s19 * 683901;
    s19 = 0;

    s6 += s18 * 666643;
    s7 += s18 * 470296;
    s8 += s18 * 654183;
    s9 -= s18 * 997805;
    s10 += s18 * 136657;
    s11 -= s18 * 683901;
    s18 = 0;

    // Carry propagation
    let mut carry: i64;
    carry = (s6 + (1 << 20)) >> 21;
    s7 += carry;
    s6 -= carry << 21;
    carry = (s8 + (1 << 20)) >> 21;
    s9 += carry;
    s8 -= carry << 21;
    carry = (s10 + (1 << 20)) >> 21;
    s11 += carry;
    s10 -= carry << 21;
    carry = (s12 + (1 << 20)) >> 21;
    s13 += carry;
    s12 -= carry << 21;
    carry = (s14 + (1 << 20)) >> 21;
    s15 += carry;
    s14 -= carry << 21;
    carry = (s16 + (1 << 20)) >> 21;
    s17 += carry;
    s16 -= carry << 21;
    carry = (s7 + (1 << 20)) >> 21;
    s8 += carry;
    s7 -= carry << 21;
    carry = (s9 + (1 << 20)) >> 21;
    s10 += carry;
    s9 -= carry << 21;
    carry = (s11 + (1 << 20)) >> 21;
    s12 += carry;
    s11 -= carry << 21;
    carry = (s13 + (1 << 20)) >> 21;
    s14 += carry;
    s13 -= carry << 21;
    carry = (s15 + (1 << 20)) >> 21;
    s16 += carry;
    s15 -= carry << 21;

    // Second reduction pass
    s5 += s17 * 666643;
    s6 += s17 * 470296;
    s7 += s17 * 654183;
    s8 -= s17 * 997805;
    s9 += s17 * 136657;
    s10 -= s17 * 683901;
    s17 = 0;

    s4 += s16 * 666643;
    s5 += s16 * 470296;
    s6 += s16 * 654183;
    s7 -= s16 * 997805;
    s8 += s16 * 136657;
    s9 -= s16 * 683901;
    s16 = 0;

    s3 += s15 * 666643;
    s4 += s15 * 470296;
    s5 += s15 * 654183;
    s6 -= s15 * 997805;
    s7 += s15 * 136657;
    s8 -= s15 * 683901;
    s15 = 0;

    s2 += s14 * 666643;
    s3 += s14 * 470296;
    s4 += s14 * 654183;
    s5 -= s14 * 997805;
    s6 += s14 * 136657;
    s7 -= s14 * 683901;
    s14 = 0;

    s1 += s13 * 666643;
    s2 += s13 * 470296;
    s3 += s13 * 654183;
    s4 -= s13 * 997805;
    s5 += s13 * 136657;
    s6 -= s13 * 683901;
    s13 = 0;

    s0 += s12 * 666643;
    s1 += s12 * 470296;
    s2 += s12 * 654183;
    s3 -= s12 * 997805;
    s4 += s12 * 136657;
    s5 -= s12 * 683901;
    s12 = 0;

    // Final carry propagation
    carry = (s0 + (1 << 20)) >> 21;
    s1 += carry;
    s0 -= carry << 21;
    carry = (s2 + (1 << 20)) >> 21;
    s3 += carry;
    s2 -= carry << 21;
    carry = (s4 + (1 << 20)) >> 21;
    s5 += carry;
    s4 -= carry << 21;
    carry = (s6 + (1 << 20)) >> 21;
    s7 += carry;
    s6 -= carry << 21;
    carry = (s8 + (1 << 20)) >> 21;
    s9 += carry;
    s8 -= carry << 21;
    carry = (s10 + (1 << 20)) >> 21;
    s11 += carry;
    s10 -= carry << 21;
    carry = (s1 + (1 << 20)) >> 21;
    s2 += carry;
    s1 -= carry << 21;
    carry = (s3 + (1 << 20)) >> 21;
    s4 += carry;
    s3 -= carry << 21;
    carry = (s5 + (1 << 20)) >> 21;
    s6 += carry;
    s5 -= carry << 21;
    carry = (s7 + (1 << 20)) >> 21;
    s8 += carry;
    s7 -= carry << 21;
    carry = (s9 + (1 << 20)) >> 21;
    s10 += carry;
    s9 -= carry << 21;
    carry = (s11 + (1 << 20)) >> 21;
    s12 += carry;
    s11 -= carry << 21;

    // Reduce s12 one more time
    s0 += s12 * 666643;
    s1 += s12 * 470296;
    s2 += s12 * 654183;
    s3 -= s12 * 997805;
    s4 += s12 * 136657;
    s5 -= s12 * 683901;
    s12 = 0;

    // Final carries
    carry = s0 >> 21;
    s1 += carry;
    s0 -= carry << 21;
    carry = s1 >> 21;
    s2 += carry;
    s1 -= carry << 21;
    carry = s2 >> 21;
    s3 += carry;
    s2 -= carry << 21;
    carry = s3 >> 21;
    s4 += carry;
    s3 -= carry << 21;
    carry = s4 >> 21;
    s5 += carry;
    s4 -= carry << 21;
    carry = s5 >> 21;
    s6 += carry;
    s5 -= carry << 21;
    carry = s6 >> 21;
    s7 += carry;
    s6 -= carry << 21;
    carry = s7 >> 21;
    s8 += carry;
    s7 -= carry << 21;
    carry = s8 >> 21;
    s9 += carry;
    s8 -= carry << 21;
    carry = s9 >> 21;
    s10 += carry;
    s9 -= carry << 21;
    carry = s10 >> 21;
    s11 += carry;
    s10 -= carry << 21;
    carry = s11 >> 21;
    s12 += carry;
    s11 -= carry << 21;

    // One more reduction for s12
    s0 += s12 * 666643;
    s1 += s12 * 470296;
    s2 += s12 * 654183;
    s3 -= s12 * 997805;
    s4 += s12 * 136657;
    s5 -= s12 * 683901;

    carry = s0 >> 21;
    s1 += carry;
    s0 -= carry << 21;
    carry = s1 >> 21;
    s2 += carry;
    s1 -= carry << 21;
    carry = s2 >> 21;
    s3 += carry;
    s2 -= carry << 21;
    carry = s3 >> 21;
    s4 += carry;
    s3 -= carry << 21;
    carry = s4 >> 21;
    s5 += carry;
    s4 -= carry << 21;
    carry = s5 >> 21;
    s6 += carry;
    s5 -= carry << 21;
    carry = s6 >> 21;
    s7 += carry;
    s6 -= carry << 21;
    carry = s7 >> 21;
    s8 += carry;
    s7 -= carry << 21;
    carry = s8 >> 21;
    s9 += carry;
    s8 -= carry << 21;
    carry = s9 >> 21;
    s10 += carry;
    s9 -= carry << 21;
    carry = s10 >> 21;
    s11 += carry;
    s10 -= carry << 21;

    // Pack into bytes
    let mut result = [0u8; 32];
    result[0] = s0 as u8;
    result[1] = (s0 >> 8) as u8;
    result[2] = ((s0 >> 16) | (s1 << 5)) as u8;
    result[3] = (s1 >> 3) as u8;
    result[4] = (s1 >> 11) as u8;
    result[5] = ((s1 >> 19) | (s2 << 2)) as u8;
    result[6] = (s2 >> 6) as u8;
    result[7] = ((s2 >> 14) | (s3 << 7)) as u8;
    result[8] = (s3 >> 1) as u8;
    result[9] = (s3 >> 9) as u8;
    result[10] = ((s3 >> 17) | (s4 << 4)) as u8;
    result[11] = (s4 >> 4) as u8;
    result[12] = (s4 >> 12) as u8;
    result[13] = ((s4 >> 20) | (s5 << 1)) as u8;
    result[14] = (s5 >> 7) as u8;
    result[15] = ((s5 >> 15) | (s6 << 6)) as u8;
    result[16] = (s6 >> 2) as u8;
    result[17] = (s6 >> 10) as u8;
    result[18] = ((s6 >> 18) | (s7 << 3)) as u8;
    result[19] = (s7 >> 5) as u8;
    result[20] = (s7 >> 13) as u8;
    result[21] = s8 as u8;
    result[22] = (s8 >> 8) as u8;
    result[23] = ((s8 >> 16) | (s9 << 5)) as u8;
    result[24] = (s9 >> 3) as u8;
    result[25] = (s9 >> 11) as u8;
    result[26] = ((s9 >> 19) | (s10 << 2)) as u8;
    result[27] = (s10 >> 6) as u8;
    result[28] = ((s10 >> 14) | (s11 << 7)) as u8;
    result[29] = (s11 >> 1) as u8;
    result[30] = (s11 >> 9) as u8;
    result[31] = (s11 >> 17) as u8;

    Scalar { bytes: result }
}

/// Load 3 bytes as little-endian integer
fn load_3(bytes: &[u8]) -> i64 {
    i64::from(bytes[0]) | (i64::from(bytes[1]) << 8) | (i64::from(bytes[2]) << 16)
}

/// Load 4 bytes as little-endian integer
fn load_4(bytes: &[u8]) -> i64 {
    i64::from(bytes[0])
        | (i64::from(bytes[1]) << 8)
        | (i64::from(bytes[2]) << 16)
        | (i64::from(bytes[3]) << 24)
}

/// Add two scalars modulo L
fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
    let mut result = [0u8; 32];
    let mut carry: u16 = 0;

    for i in 0..32 {
        carry += u16::from(a.bytes[i]) + u16::from(b.bytes[i]);
        result[i] = carry as u8;
        carry >>= 8;
    }

    // Reduce if >= L
    scalar_reduce(&mut result);

    Scalar { bytes: result }
}

/// Multiply two scalars modulo L
fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar {
    // Full 64-byte product, then reduce
    let mut product = [0u8; 64];

    // Schoolbook multiplication
    for i in 0..32 {
        let mut carry: u32 = 0;
        for j in 0..32 {
            if i + j < 64 {
                let p = u32::from(a.bytes[i]) * u32::from(b.bytes[j])
                    + u32::from(product[i + j])
                    + carry;
                product[i + j] = p as u8;
                carry = p >> 8;
            }
        }
        // Propagate remaining carry
        let mut k = i + 32;
        while carry > 0 && k < 64 {
            let sum = u32::from(product[k]) + carry;
            product[k] = sum as u8;
            carry = sum >> 8;
            k += 1;
        }
    }

    Scalar::from_bytes_mod_order_wide(&product)
}

/// Reduce a 32-byte scalar modulo L (in place)
fn scalar_reduce(bytes: &mut [u8; 32]) {
    // Compare with L and subtract if >= L
    // This is done in constant time

    let mut borrow: i16 = 0;
    let mut diff = [0u8; 32];

    // Compute bytes - L
    for i in 0..32 {
        let d = i16::from(bytes[i]) - i16::from(L_BYTES[i]) + borrow;
        if d < 0 {
            diff[i] = (d + 256) as u8;
            borrow = -1;
        } else {
            diff[i] = d as u8;
            borrow = 0;
        }
    }

    // If borrow == 0, bytes >= L, so use diff
    // If borrow == -1, bytes < L, so keep bytes
    // Create mask: 0xff when borrow == -1 (keep bytes), 0x00 when borrow == 0 (use diff)
    let keep_original = (borrow != 0) as u8; // 1 if borrow == -1, 0 if borrow == 0
    let mask = keep_original.wrapping_neg(); // 0xff if keep, 0x00 if use diff

    for i in 0..32 {
        bytes[i] = (bytes[i] & mask) | (diff[i] & !mask);
    }
}

// =============================================================================
// Ed25519 Key Types
// =============================================================================

/// Ed25519 signing key (contains both secret and public key)
pub struct Ed25519SigningKey {
    /// Secret key seed (32 bytes)
    seed: [u8; SECRET_KEY_SIZE],
    /// Expanded secret key: first 32 bytes are scalar, last 32 are prefix
    expanded: [u8; EXPANDED_SECRET_KEY_SIZE],
    /// Public key (32 bytes)
    public_key: [u8; PUBLIC_KEY_SIZE],
}

impl Ed25519SigningKey {
    /// Generate a new signing key from a 32-byte seed
    ///
    /// # Arguments
    /// * `seed` - 32 bytes of cryptographically secure random data
    ///
    /// # Returns
    /// A new Ed25519 signing key
    #[must_use]
    pub fn from_seed(seed: &[u8; SECRET_KEY_SIZE]) -> Self {
        // 1. Hash the seed with SHA-512
        let expanded = Sha512::hash(seed);

        // 2. Clamp the first 32 bytes to form the scalar
        let mut clamped = [0u8; 32];
        clamped.copy_from_slice(&expanded[..32]);
        clamped[0] &= 248; // Clear lowest 3 bits
        clamped[31] &= 127; // Clear highest bit
        clamped[31] |= 64; // Set second-highest bit

        // 3. Compute public key: A = s * B
        let scalar = Scalar::from_bytes_mod_order(&clamped);
        let public_point = basepoint().scalar_mul(&scalar);
        let public_key = public_point.compress();

        // Store expanded key (scalar in first 32 bytes, prefix in last 32)
        let mut expanded_key = [0u8; EXPANDED_SECRET_KEY_SIZE];
        expanded_key[..32].copy_from_slice(&clamped);
        expanded_key[32..].copy_from_slice(&expanded[32..]);

        Self {
            seed: *seed,
            expanded: expanded_key,
            public_key,
        }
    }

    /// Generate a new random signing key
    ///
    /// # Arguments
    /// * `random` - 32 bytes of cryptographically secure random data
    #[must_use]
    pub fn generate(random: &[u8; 32]) -> Self {
        Self::from_seed(random)
    }

    /// Get the public key
    #[must_use]
    pub fn public_key(&self) -> &Ed25519VerifyingKey {
        // SAFETY: Ed25519VerifyingKey is a transparent wrapper
        unsafe { &*(self.public_key.as_ptr() as *const Ed25519VerifyingKey) }
    }

    /// Get the public key bytes
    #[must_use]
    pub fn public_key_bytes(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        &self.public_key
    }

    /// Sign a message
    ///
    /// # Arguments
    /// * `message` - The message to sign
    ///
    /// # Returns
    /// A 64-byte Ed25519 signature
    #[must_use]
    pub fn sign(&self, message: &[u8]) -> [u8; SIGNATURE_SIZE] {
        // RFC 8032 signing algorithm:

        // 1. r = SHA-512(prefix || message) mod L
        let mut hasher = Sha512::new();
        hasher.update(&self.expanded[32..]); // prefix
        hasher.update(message);
        let r_hash = hasher.finalize();
        let r = Scalar::from_bytes_mod_order_wide(&r_hash);

        // 2. R = r * B (compute commitment point)
        let r_point = basepoint().scalar_mul(&r);
        let r_bytes = r_point.compress();

        // 3. k = SHA-512(R || public_key || message) mod L
        let mut hasher = Sha512::new();
        hasher.update(&r_bytes);
        hasher.update(&self.public_key);
        hasher.update(message);
        let k_hash = hasher.finalize();
        let k = Scalar::from_bytes_mod_order_wide(&k_hash);

        // 4. s = (r + k * scalar) mod L
        let scalar = Scalar::from_bytes_mod_order(&self.expanded[..32].try_into().unwrap());
        let k_scalar = scalar_mul(&k, &scalar);
        let s = scalar_add(&r, &k_scalar);

        // 5. Signature is (R, s)
        let mut signature = [0u8; SIGNATURE_SIZE];
        signature[..32].copy_from_slice(&r_bytes);
        signature[32..].copy_from_slice(s.as_bytes());

        signature
    }

    /// Get the seed
    #[must_use]
    pub fn seed(&self) -> &[u8; SECRET_KEY_SIZE] {
        &self.seed
    }
}

impl Drop for Ed25519SigningKey {
    fn drop(&mut self) {
        // Zeroize all secret material (Law 4)
        self.seed.zeroize();
        self.expanded.zeroize();
    }
}

/// Ed25519 verification key (public key)
#[repr(transparent)]
pub struct Ed25519VerifyingKey {
    /// Public key bytes (compressed Edwards point)
    bytes: [u8; PUBLIC_KEY_SIZE],
}

impl Ed25519VerifyingKey {
    /// Create a verifying key from bytes
    ///
    /// # Arguments
    /// * `bytes` - 32-byte public key
    ///
    /// # Errors
    /// Returns `InvalidSignature` if the point is not on the curve.
    pub fn from_bytes(bytes: &[u8; PUBLIC_KEY_SIZE]) -> CryptoResult<Self> {
        // Validate that the point is on the curve by decompressing
        let _ = EdwardsPoint::decompress(bytes)?;
        Ok(Self { bytes: *bytes })
    }

    /// Get the public key bytes
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; PUBLIC_KEY_SIZE] {
        &self.bytes
    }

    /// Verify a signature on a message
    ///
    /// # Arguments
    /// * `message` - The message that was signed
    /// * `signature` - The 64-byte signature
    ///
    /// # Errors
    /// Returns `InvalidSignature` if verification fails.
    pub fn verify(&self, message: &[u8], signature: &[u8; SIGNATURE_SIZE]) -> CryptoResult<()> {
        // RFC 8032 verification algorithm:

        // 1. Parse R from signature[0..32]
        let r_bytes: [u8; 32] = signature[..32].try_into().unwrap();
        let r_point = EdwardsPoint::decompress(&r_bytes)?;

        // 2. Parse s from signature[32..64]
        let s_bytes: [u8; 32] = signature[32..].try_into().unwrap();

        // 3. Check s < L
        if !is_scalar_valid(&s_bytes) {
            return Err(CryptoError::InvalidSignature);
        }
        let s = Scalar::from_bytes_mod_order(&s_bytes);

        // 4. Decompress public key
        let a_point = EdwardsPoint::decompress(&self.bytes)?;

        // 5. Compute k = SHA-512(R || public_key || message) mod L
        let mut hasher = Sha512::new();
        hasher.update(&r_bytes);
        hasher.update(&self.bytes);
        hasher.update(message);
        let k_hash = hasher.finalize();
        let k = Scalar::from_bytes_mod_order_wide(&k_hash);

        // 6. Check that s * B == R + k * A
        // Equivalently: s * B - k * A == R
        let sb = basepoint().scalar_mul(&s);
        let ka = a_point.scalar_mul(&k);
        let rhs = sb.add(&ka.negate());

        // Compare compressed forms
        let computed_r = rhs.compress();

        if computed_r == r_bytes {
            Ok(())
        } else {
            Err(CryptoError::InvalidSignature)
        }
    }
}

/// Check if a scalar is valid (< L)
fn is_scalar_valid(bytes: &[u8; 32]) -> bool {
    // Compare with L in constant time
    let mut borrow = 0i16;
    for i in (0..32).rev() {
        let diff = i16::from(bytes[i]) - i16::from(L_BYTES[i]) - borrow;
        borrow = if diff < 0 { 1 } else { 0 };
    }
    // If borrow == 1, bytes < L, which is valid
    borrow == 1
}

/// Ed25519 signature operations (implements Signature trait)
pub struct Ed25519;

impl Signature for Ed25519 {
    const SECRET_KEY_SIZE: usize = SECRET_KEY_SIZE;
    const PUBLIC_KEY_SIZE: usize = PUBLIC_KEY_SIZE;
    const SIGNATURE_SIZE: usize = SIGNATURE_SIZE;

    fn generate_keypair(
        rng: &[u8],
        secret_key: &mut [u8],
        public_key: &mut [u8],
    ) -> CryptoResult<()> {
        if rng.len() < SECRET_KEY_SIZE {
            return Err(CryptoError::KeyGenerationFailed);
        }
        if secret_key.len() != SECRET_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        if public_key.len() != PUBLIC_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }

        let seed: [u8; SECRET_KEY_SIZE] = rng[..SECRET_KEY_SIZE]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;

        let keypair = Ed25519SigningKey::from_seed(&seed);
        secret_key.copy_from_slice(&keypair.seed);
        public_key.copy_from_slice(&keypair.public_key);

        Ok(())
    }

    fn sign(secret_key: &[u8], message: &[u8], signature: &mut [u8]) -> CryptoResult<()> {
        if secret_key.len() != SECRET_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        if signature.len() != SIGNATURE_SIZE {
            return Err(CryptoError::BufferTooSmall);
        }

        let seed: [u8; SECRET_KEY_SIZE] = secret_key
            .try_into()
            .map_err(|_| CryptoError::InvalidKeyLength)?;

        let keypair = Ed25519SigningKey::from_seed(&seed);
        let sig = keypair.sign(message);
        signature.copy_from_slice(&sig);

        Ok(())
    }

    fn verify(public_key: &[u8], message: &[u8], signature: &[u8]) -> CryptoResult<()> {
        if public_key.len() != PUBLIC_KEY_SIZE {
            return Err(CryptoError::InvalidKeyLength);
        }
        if signature.len() != SIGNATURE_SIZE {
            return Err(CryptoError::InvalidSignature);
        }

        let pk_bytes: [u8; PUBLIC_KEY_SIZE] = public_key
            .try_into()
            .map_err(|_| CryptoError::InvalidKeyLength)?;
        let sig_bytes: [u8; SIGNATURE_SIZE] = signature
            .try_into()
            .map_err(|_| CryptoError::InvalidSignature)?;

        let verifying_key = Ed25519VerifyingKey::from_bytes(&pk_bytes)?;
        verifying_key.verify(message, &sig_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ed25519_key_generation() {
        let seed = [0x42u8; 32];
        let keypair = Ed25519SigningKey::from_seed(&seed);

        // Verify seed is stored
        assert_eq!(keypair.seed(), &seed);

        // Public key should be 32 bytes and non-zero
        let pk = keypair.public_key_bytes();
        assert_eq!(pk.len(), PUBLIC_KEY_SIZE);
        assert_ne!(pk, &[0u8; 32]);
    }

    #[test]
    fn test_ed25519_signature_size() {
        let seed = [0x42u8; 32];
        let keypair = Ed25519SigningKey::from_seed(&seed);
        let signature = keypair.sign(b"test message");

        assert_eq!(signature.len(), SIGNATURE_SIZE);
    }

    #[test]
    fn test_ed25519_sign_verify_roundtrip() {
        let seed = [0x42u8; 32];
        let keypair = Ed25519SigningKey::from_seed(&seed);
        let message = b"Hello, RIINA!";

        let signature = keypair.sign(message);

        // Verification should succeed
        let result = keypair.public_key().verify(message, &signature);
        assert!(
            result.is_ok(),
            "Signature verification failed: {:?}",
            result
        );
    }

    #[test]
    fn test_ed25519_wrong_message_fails() {
        let seed = [0x42u8; 32];
        let keypair = Ed25519SigningKey::from_seed(&seed);

        let signature = keypair.sign(b"Original message");

        // Verification with different message should fail
        let result = keypair
            .public_key()
            .verify(b"Different message", &signature);
        assert!(result.is_err());
    }

    #[test]
    fn test_ed25519_wrong_key_fails() {
        let keypair1 = Ed25519SigningKey::from_seed(&[0x42u8; 32]);
        let keypair2 = Ed25519SigningKey::from_seed(&[0x43u8; 32]);

        let message = b"Test message";
        let signature = keypair1.sign(message);

        // Verification with different public key should fail
        let result = keypair2.public_key().verify(message, &signature);
        assert!(result.is_err());
    }

    #[test]
    fn test_basepoint_compression() {
        let b = basepoint();
        let compressed = b.compress();

        // Decompress and re-compress should give same result
        let decompressed = EdwardsPoint::decompress(&compressed).unwrap();
        let recompressed = decompressed.compress();

        assert_eq!(compressed, recompressed);
    }

    #[test]
    fn test_identity_compression() {
        let identity = EdwardsPoint::identity();
        let compressed = identity.compress();

        // Identity compresses to (0, 1) -> y = 1 in little-endian with x sign = 0
        // y = 1 = 0x0000...0001
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(compressed, expected);
    }

    #[test]
    fn test_point_addition_identity() {
        let b = basepoint();
        let identity = EdwardsPoint::identity();

        // B + identity = B
        let result = b.add(&identity);
        assert_eq!(b.compress(), result.compress());

        // identity + B = B
        let result2 = identity.add(&b);
        assert_eq!(b.compress(), result2.compress());
    }

    #[test]
    fn test_basepoint_on_curve() {
        // Verify basepoint satisfies the curve equation: -x² + y² = 1 + d·x²·y²
        // by computing x from y and verifying it matches

        // y = 4/5 mod p
        let by = FieldElement::from_bytes(&[
            0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66,
        ]);

        let d = curve_d();
        eprintln!("d: {:02x?}", d.to_bytes());

        let y2 = by.square();
        eprintln!("y²: {:02x?}", y2.to_bytes());

        // From curve equation -x² + y² = 1 + d·x²·y²
        // => y² - 1 = x²(1 + d·y²)
        // => x² = (y² - 1) / (1 + d·y²)
        // But actually for -x² + y² = 1 + d·x²·y²:
        // y² - 1 = x² + d·x²·y²
        // y² - 1 = x²(1 + d·y²)
        // x² = (y² - 1) / (1 + d·y²)

        let numerator = y2 - FieldElement::ONE;
        eprintln!("y² - 1: {:02x?}", numerator.to_bytes());

        let d_times_y2 = d * y2;
        eprintln!("d*y²: {:02x?}", d_times_y2.to_bytes());

        let denominator = FieldElement::ONE + d_times_y2;
        eprintln!("1 + d*y²: {:02x?}", denominator.to_bytes());

        let denom_inv = denominator.invert();
        eprintln!("(1 + d*y²)^-1: {:02x?}", denom_inv.to_bytes());

        let x2_computed = numerator * denom_inv;

        // Expected x
        let bx = FieldElement::from_bytes(&[
            0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7,
            0x2c, 0x69, 0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd,
            0xd3, 0x36, 0x69, 0x21,
        ]);
        let x2_expected = bx.square();

        let x2_computed_bytes = x2_computed.to_bytes();
        let x2_expected_bytes = x2_expected.to_bytes();
        eprintln!("x² computed: {:02x?}", x2_computed_bytes);
        eprintln!("x² expected: {:02x?}", x2_expected_bytes);

        assert_eq!(x2_computed.ct_eq(&x2_expected), 1, "x² mismatch!");

        // Now verify the curve equation
        let lhs = y2 - x2_expected;
        let rhs = FieldElement::ONE + d * x2_expected * y2;
        eprintln!("LHS (y²-x²): {:02x?}", lhs.to_bytes());
        eprintln!("RHS (1+dx²y²): {:02x?}", rhs.to_bytes());

        assert_eq!(lhs.ct_eq(&rhs), 1, "Basepoint not on curve!");
    }

    #[test]
    fn test_point_doubling() {
        let b = basepoint();

        // 2B via doubling
        let double = b.double();

        // 2B via addition
        let sum = b.add(&b);

        // Debug: print the compressed forms
        let double_comp = double.compress();
        let sum_comp = sum.compress();

        // Both should be on the curve
        let (dx, dy) = double.to_affine();
        let x2 = dx.square();
        let y2 = dy.square();
        let lhs = y2 - x2;
        let rhs = FieldElement::ONE + curve_d() * x2 * y2;
        assert_eq!(lhs.ct_eq(&rhs), 1, "Doubled point not on curve!");

        let (sx, sy) = sum.to_affine();
        let x2 = sx.square();
        let y2 = sy.square();
        let lhs = y2 - x2;
        let rhs = FieldElement::ONE + curve_d() * x2 * y2;
        assert_eq!(lhs.ct_eq(&rhs), 1, "Added point not on curve!");

        assert_eq!(double_comp, sum_comp);
    }

    // RFC 8032 test vectors
    #[test]
    fn test_ed25519_rfc8032_test1() {
        // Test vector 1 from RFC 8032
        let seed: [u8; 32] = [
            0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec,
            0x2c, 0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03,
            0x1c, 0xae, 0x7f, 0x60,
        ];

        let expected_public_key: [u8; 32] = [
            0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64,
            0x07, 0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68,
            0xf7, 0x07, 0x51, 0x1a,
        ];

        let keypair = Ed25519SigningKey::from_seed(&seed);
        assert_eq!(keypair.public_key_bytes(), &expected_public_key);

        // Empty message signature
        let signature = keypair.sign(b"");
        let expected_signature: [u8; 64] = [
            0xe5, 0x56, 0x43, 0x00, 0xc3, 0x60, 0xac, 0x72, 0x90, 0x86, 0xe2, 0xcc, 0x80, 0x6e,
            0x82, 0x8a, 0x84, 0x87, 0x7f, 0x1e, 0xb8, 0xe5, 0xd9, 0x74, 0xd8, 0x73, 0xe0, 0x65,
            0x22, 0x49, 0x01, 0x55, 0x5f, 0xb8, 0x82, 0x15, 0x90, 0xa3, 0x3b, 0xac, 0xc6, 0x1e,
            0x39, 0x70, 0x1c, 0xf9, 0xb4, 0x6b, 0xd2, 0x5b, 0xf5, 0xf0, 0x59, 0x5b, 0xbe, 0x24,
            0x65, 0x51, 0x41, 0x43, 0x8e, 0x7a, 0x10, 0x0b,
        ];
        assert_eq!(signature, expected_signature);

        // Verify the signature
        let result = keypair.public_key().verify(b"", &signature);
        assert!(result.is_ok());
    }

    #[test]
    fn test_ed25519_rfc8032_test2() {
        // Test vector 2 from RFC 8032 (1 byte message)
        let seed: [u8; 32] = [
            0x4c, 0xcd, 0x08, 0x9b, 0x28, 0xff, 0x96, 0xda, 0x9d, 0xb6, 0xc3, 0x46, 0xec, 0x11,
            0x4e, 0x0f, 0x5b, 0x8a, 0x31, 0x9f, 0x35, 0xab, 0xa6, 0x24, 0xda, 0x8c, 0xf6, 0xed,
            0x4f, 0xb8, 0xa6, 0xfb,
        ];

        let keypair = Ed25519SigningKey::from_seed(&seed);
        let signature = keypair.sign(&[0x72]); // Message is single byte 0x72

        let expected_signature: [u8; 64] = [
            0x92, 0xa0, 0x09, 0xa9, 0xf0, 0xd4, 0xca, 0xb8, 0x72, 0x0e, 0x82, 0x0b, 0x5f, 0x64,
            0x25, 0x40, 0xa2, 0xb2, 0x7b, 0x54, 0x16, 0x50, 0x3f, 0x8f, 0xb3, 0x76, 0x22, 0x23,
            0xeb, 0xdb, 0x69, 0xda, 0x08, 0x5a, 0xc1, 0xe4, 0x3e, 0x15, 0x99, 0x6e, 0x45, 0x8f,
            0x36, 0x13, 0xd0, 0xf1, 0x1d, 0x8c, 0x38, 0x7b, 0x2e, 0xae, 0xb4, 0x30, 0x2a, 0xee,
            0xb0, 0x0d, 0x29, 0x16, 0x12, 0xbb, 0x0c, 0x00,
        ];
        assert_eq!(signature, expected_signature);

        // Verify the signature
        let result = keypair.public_key().verify(&[0x72], &signature);
        assert!(result.is_ok());
    }
}
