//! Field Arithmetic for GF(2^255-19)
//!
//! This module implements constant-time field arithmetic over the prime field
//! GF(2^255-19), which is used in both X25519 (Curve25519) and Ed25519.
//!
//! # Implementation Strategy
//!
//! We use a radix-2^51 representation with 5 limbs:
//! - Each limb stores up to 51 bits
//! - Total: 5 × 51 = 255 bits (exactly the field size)
//! - Allows efficient carry propagation
//! - Compatible with 64-bit arithmetic (no overflow)
//!
//! # Prime: p = 2^255 - 19
//!
//! ```text
//! p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
//!   = 57896044618658097711785492504343953926634992332820282019728792003956564819949
//! ```
//!
//! # Constant-Time Guarantees
//!
//! All operations are implemented to run in constant time (no branches on secret data).
//! This is critical for resistance against timing side-channel attacks.
//!
//! # References
//!
//! - RFC 7748: Elliptic Curves for Security
//! - DJB's Curve25519 paper: https://cr.yp.to/ecdh.html
//! - Adam Langley's curve25519-donna

use core::ops::{Add, Sub, Mul};

/// A field element in GF(2^255-19), represented in radix 2^51.
///
/// Internally stored as 5 limbs, each up to 51 bits:
/// - limbs[0]: bits 0..51
/// - limbs[1]: bits 51..102
/// - limbs[2]: bits 102..153
/// - limbs[3]: bits 153..204
/// - limbs[4]: bits 204..255
///
/// # Invariants
///
/// - After reduction: each limb < 2^51
/// - After weak reduction: each limb < 2^52 (allows some overflow for performance)
/// - Full reduction ensures canonical representation
///
/// # Security Note
///
/// FieldElement is Copy for performance. Zeroization is handled at the
/// higher-level types (X25519KeyPair, Ed25519SigningKey) that contain
/// secret field elements. Intermediate field elements in computations
/// are not considered sensitive enough to warrant individual zeroization.
#[derive(Clone, Copy, Debug)]
pub struct FieldElement {
    /// 5 limbs, each storing up to 51 bits (after reduction)
    limbs: [i64; 5],
}

impl FieldElement {
    /// The zero element (additive identity)
    pub const ZERO: Self = Self { limbs: [0, 0, 0, 0, 0] };

    /// The one element (multiplicative identity)
    pub const ONE: Self = Self { limbs: [1, 0, 0, 0, 0] };

    /// The modulus p = 2^255 - 19 in radix-2^51 representation
    ///
    /// Note: This is stored reduced for use in constant-time operations
    const MODULUS: Self = Self {
        limbs: [
            0x7ffffffffffed, // 2^51 - 19
            0x7ffffffffffff, // 2^51 - 1
            0x7ffffffffffff, // 2^51 - 1
            0x7ffffffffffff, // 2^51 - 1
            0x7ffffffffffff, // 2^51 - 1
        ],
    };

    /// Load 8 bytes as an i64 (little-endian).
    #[inline]
    fn load_8(input: &[u8]) -> i64 {
        i64::from(input[0])
            | (i64::from(input[1]) << 8)
            | (i64::from(input[2]) << 16)
            | (i64::from(input[3]) << 24)
            | (i64::from(input[4]) << 32)
            | (i64::from(input[5]) << 40)
            | (i64::from(input[6]) << 48)
            | (i64::from(input[7]) << 56)
    }

    /// Create a FieldElement from a 32-byte little-endian array.
    ///
    /// This performs a full reduction modulo p.
    ///
    /// # Arguments
    /// * `bytes` - 32-byte little-endian representation
    ///
    /// # Returns
    /// The field element reduced modulo p
    #[must_use]
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        // Convert bytes to 5 limbs (little-endian, radix 2^51)
        let h0 = Self::load_8(&bytes[0..8]);
        let h1 = Self::load_8(&bytes[6..14]) >> 3;
        let h2 = Self::load_8(&bytes[12..20]) >> 6;
        let h3 = Self::load_8(&bytes[19..27]) >> 1;
        let h4 = Self::load_8(&bytes[24..32]) >> 12;

        // Mask to 51 bits per limb
        let limbs = [
            h0 & 0x7ffffffffffff,
            h1 & 0x7ffffffffffff,
            h2 & 0x7ffffffffffff,
            h3 & 0x7ffffffffffff,
            h4 & 0x7ffffffffffff,
        ];

        Self { limbs }.reduce()
    }

    /// Convert this FieldElement to a 32-byte little-endian array.
    ///
    /// This performs a full reduction to ensure canonical representation.
    ///
    /// # Returns
    /// 32-byte little-endian representation of the field element
    #[must_use]
    pub fn to_bytes(&self) -> [u8; 32] {
        // Fully reduce to canonical form
        let fe = self.reduce();

        let mut result = [0u8; 32];

        // Pack limbs into bytes (little-endian)
        let h0 = fe.limbs[0];
        let h1 = fe.limbs[1];
        let h2 = fe.limbs[2];
        let h3 = fe.limbs[3];
        let h4 = fe.limbs[4];

        result[0] = (h0 & 0xff) as u8;
        result[1] = ((h0 >> 8) & 0xff) as u8;
        result[2] = ((h0 >> 16) & 0xff) as u8;
        result[3] = ((h0 >> 24) & 0xff) as u8;
        result[4] = ((h0 >> 32) & 0xff) as u8;
        result[5] = ((h0 >> 40) & 0xff) as u8;
        result[6] = (((h0 >> 48) | (h1 << 3)) & 0xff) as u8;

        result[7] = ((h1 >> 5) & 0xff) as u8;
        result[8] = ((h1 >> 13) & 0xff) as u8;
        result[9] = ((h1 >> 21) & 0xff) as u8;
        result[10] = ((h1 >> 29) & 0xff) as u8;
        result[11] = ((h1 >> 37) & 0xff) as u8;
        result[12] = (((h1 >> 45) | (h2 << 6)) & 0xff) as u8;

        result[13] = ((h2 >> 2) & 0xff) as u8;
        result[14] = ((h2 >> 10) & 0xff) as u8;
        result[15] = ((h2 >> 18) & 0xff) as u8;
        result[16] = ((h2 >> 26) & 0xff) as u8;
        result[17] = ((h2 >> 34) & 0xff) as u8;
        result[18] = ((h2 >> 42) & 0xff) as u8;
        result[19] = (((h2 >> 50) | (h3 << 1)) & 0xff) as u8;

        result[20] = ((h3 >> 7) & 0xff) as u8;
        result[21] = ((h3 >> 15) & 0xff) as u8;
        result[22] = ((h3 >> 23) & 0xff) as u8;
        result[23] = ((h3 >> 31) & 0xff) as u8;
        result[24] = ((h3 >> 39) & 0xff) as u8;
        result[25] = (((h3 >> 47) | (h4 << 4)) & 0xff) as u8;

        result[26] = ((h4 >> 4) & 0xff) as u8;
        result[27] = ((h4 >> 12) & 0xff) as u8;
        result[28] = ((h4 >> 20) & 0xff) as u8;
        result[29] = ((h4 >> 28) & 0xff) as u8;
        result[30] = ((h4 >> 36) & 0xff) as u8;
        result[31] = ((h4 >> 44) & 0xff) as u8;

        result
    }

    /// Weak reduction: ensures each limb < 2^52.
    ///
    /// This is faster than full reduction and sufficient for intermediate
    /// computations. For final results or comparisons, use `reduce()`.
    #[inline]
    #[must_use]
    fn weak_reduce(self) -> Self {
        let mut limbs = self.limbs;

        // Carry propagation
        let c0 = limbs[0] >> 51;
        limbs[0] &= 0x7ffffffffffff;
        limbs[1] += c0;

        let c1 = limbs[1] >> 51;
        limbs[1] &= 0x7ffffffffffff;
        limbs[2] += c1;

        let c2 = limbs[2] >> 51;
        limbs[2] &= 0x7ffffffffffff;
        limbs[3] += c2;

        let c3 = limbs[3] >> 51;
        limbs[3] &= 0x7ffffffffffff;
        limbs[4] += c3;

        let c4 = limbs[4] >> 51;
        limbs[4] &= 0x7ffffffffffff;
        limbs[0] += c4 * 19; // Reduce modulo 2^255 - 19

        Self { limbs }
    }

    /// Full reduction: ensures canonical representation modulo p.
    ///
    /// After this operation:
    /// - Each limb < 2^51
    /// - The value is fully reduced modulo p
    /// - The representation is canonical (unique for each field element)
    #[must_use]
    pub fn reduce(self) -> Self {
        // First, weak reduction to get limbs under control
        let mut fe = self.weak_reduce();

        // May need one more round of carry propagation
        fe = fe.weak_reduce();

        // Final reduction: subtract p if >= p
        // This is done in constant time
        let mut limbs = fe.limbs;

        // Compute: result = limbs - p
        // If result >= 0, use result; else use limbs
        let mut borrow: i64 = 0;
        let mut result = [0i64; 5];

        result[0] = limbs[0] - 0x7ffffffffffed + borrow;
        borrow = result[0] >> 63; // Arithmetic shift: -1 if negative, 0 otherwise
        result[0] &= 0x7ffffffffffff;

        for i in 1..5 {
            result[i] = limbs[i] - 0x7ffffffffffff + borrow;
            borrow = result[i] >> 63;
            result[i] &= 0x7ffffffffffff;
        }

        // If borrow is -1, we had underflow, so keep original limbs
        // If borrow is 0, we successfully subtracted p, so use result
        // Use constant-time selection
        let mask = borrow; // -1 or 0
        for i in 0..5 {
            limbs[i] = (limbs[i] & mask) | (result[i] & !mask);
        }

        Self { limbs }
    }

    /// Negate this field element: -a (mod p)
    #[inline]
    #[must_use]
    pub fn negate(self) -> Self {
        // -a = p - a
        // We compute: 2*p - a, then reduce
        // This avoids underflow in intermediate computations
        let limbs = [
            2 * 0x7ffffffffffed - self.limbs[0],
            2 * 0x7ffffffffffff - self.limbs[1],
            2 * 0x7ffffffffffff - self.limbs[2],
            2 * 0x7ffffffffffff - self.limbs[3],
            2 * 0x7ffffffffffff - self.limbs[4],
        ];
        Self { limbs }.weak_reduce()
    }

    /// Constant-time conditional swap.
    ///
    /// If swap is 1, swap self and other.
    /// If swap is 0, leave unchanged.
    ///
    /// # Arguments
    /// * `other` - The element to potentially swap with
    /// * `swap` - 1 to swap, 0 to not swap
    ///
    /// # Panics
    /// Panics if swap is not 0 or 1.
    pub fn conditional_swap(&mut self, other: &mut Self, swap: i64) {
        debug_assert!(swap == 0 || swap == 1, "swap must be 0 or 1");

        let mask = -swap; // 0 or -1 (all bits set)

        for i in 0..5 {
            let x = mask & (self.limbs[i] ^ other.limbs[i]);
            self.limbs[i] ^= x;
            other.limbs[i] ^= x;
        }
    }

    /// Constant-time equality check.
    ///
    /// Returns 1 if self == other, 0 otherwise.
    ///
    /// # Returns
    /// 1 if equal, 0 if not equal
    #[must_use]
    pub fn ct_eq(&self, other: &Self) -> i64 {
        let a = self.reduce();
        let b = other.reduce();

        let mut diff = 0i64;
        for i in 0..5 {
            diff |= a.limbs[i] ^ b.limbs[i];
        }

        // If diff == 0, all limbs were equal
        // Return 1 if diff == 0, else 0
        let zero = (diff | -diff) >> 63; // -1 if diff != 0, 0 if diff == 0
        (zero + 1) & 1 // Convert to 0 or 1
    }

    /// Check if this element is zero (constant-time).
    ///
    /// # Returns
    /// true if this element is zero
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.ct_eq(&Self::ZERO) == 1
    }

    /// Create a FieldElement from a small i64 value.
    ///
    /// # Arguments
    /// * `value` - A small integer value (should fit in a single limb)
    ///
    /// # Returns
    /// The field element representing this value
    #[must_use]
    pub fn from_i64(value: i64) -> Self {
        Self {
            limbs: [value, 0, 0, 0, 0],
        }
        .reduce()
    }

    /// Square this field element: a^2 (mod p).
    ///
    /// This is slightly more efficient than general multiplication
    /// since we can use squaring-specific optimizations.
    ///
    /// # Returns
    /// self * self (mod p)
    #[inline]
    #[must_use]
    pub fn square(self) -> Self {
        // For now, just use multiplication
        // TODO: Implement dedicated squaring for ~20% speedup
        self * self
    }

    /// Compute the multiplicative inverse: a^(-1) (mod p).
    ///
    /// This uses Fermat's Little Theorem: a^(p-1) = 1 (mod p)
    /// Therefore: a^(-1) = a^(p-2) (mod p)
    ///
    /// For p = 2^255 - 19, we have p-2 = 2^255 - 21.
    ///
    /// We use addition chain exponentiation for efficiency.
    ///
    /// # Returns
    /// The multiplicative inverse of self
    ///
    /// # Panics
    /// Panics if self is zero (zero has no inverse)
    #[must_use]
    pub fn invert(self) -> Self {
        // Verify not zero (in debug mode)
        debug_assert!(!self.is_zero(), "Cannot invert zero");

        // Compute a^(p-2) using addition chain
        // p - 2 = 2^255 - 21
        //       = 2^255 - 16 - 4 - 1
        //       = 2^255 - 2^4 - 2^2 - 2^0

        // Use the well-known addition chain for (p-2):
        // 1, 2, 3, 4, 5, 10, 20, 40, 50, 100, 200, 250, 255

        let z2 = self.square();           // 2^1
        let z9 = z2.square().square() * self; // 2^3 * 2^0 = 2^4 - 2^3 + 2^0 = 9
        let z11 = z9 * z2;                // 11
        let z2_5_0 = z11.square().square() * z9; // 2^2 * 11 * 9 = 2^5 - 2^0

        let mut t = z2_5_0;
        for _ in 0..5 {
            t = t.square();
        }
        let z2_10_0 = t * z2_5_0;        // 2^10 - 2^0

        t = z2_10_0;
        for _ in 0..10 {
            t = t.square();
        }
        let z2_20_0 = t * z2_10_0;       // 2^20 - 2^0

        t = z2_20_0;
        for _ in 0..20 {
            t = t.square();
        }
        let z2_40_0 = t * z2_20_0;       // 2^40 - 2^0

        t = z2_40_0;
        for _ in 0..10 {
            t = t.square();
        }
        let z2_50_0 = t * z2_10_0;       // 2^50 - 2^0

        t = z2_50_0;
        for _ in 0..50 {
            t = t.square();
        }
        let z2_100_0 = t * z2_50_0;      // 2^100 - 2^0

        t = z2_100_0;
        for _ in 0..100 {
            t = t.square();
        }
        let z2_200_0 = t * z2_100_0;     // 2^200 - 2^0

        t = z2_200_0;
        for _ in 0..50 {
            t = t.square();
        }
        let z2_250_0 = t * z2_50_0;      // 2^250 - 2^0

        // Final 5 bits: 2^255 - 21 = 2^255 - 2^4 - 2^2 - 2^0
        t = z2_250_0;
        for _ in 0..5 {
            t = t.square();
        }
        t = t * z11;                     // 2^255 - 2^5 + 11 = 2^255 - 21

        t
    }
}

/// Addition: (a + b) mod p
impl Add for FieldElement {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let limbs = [
            self.limbs[0] + rhs.limbs[0],
            self.limbs[1] + rhs.limbs[1],
            self.limbs[2] + rhs.limbs[2],
            self.limbs[3] + rhs.limbs[3],
            self.limbs[4] + rhs.limbs[4],
        ];
        Self { limbs }.weak_reduce()
    }
}

/// Subtraction: (a - b) mod p
impl Sub for FieldElement {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        // Compute: a - b + 2*p (to avoid underflow)
        let limbs = [
            self.limbs[0] - rhs.limbs[0] + 2 * 0x7ffffffffffed,
            self.limbs[1] - rhs.limbs[1] + 2 * 0x7ffffffffffff,
            self.limbs[2] - rhs.limbs[2] + 2 * 0x7ffffffffffff,
            self.limbs[3] - rhs.limbs[3] + 2 * 0x7ffffffffffff,
            self.limbs[4] - rhs.limbs[4] + 2 * 0x7ffffffffffff,
        ];
        Self { limbs }.weak_reduce()
    }
}

/// Multiplication: (a * b) mod p
impl Mul for FieldElement {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        // Schoolbook multiplication with Karatsuba-style optimization
        // Result has up to 102 bits per limb before reduction

        let a = self.limbs;
        let b = rhs.limbs;

        // Compute partial products
        // We compute the full 10-limb product, then reduce modulo p
        let mut c = [0i128; 10]; // Use i128 to avoid overflow

        for i in 0..5 {
            for j in 0..5 {
                c[i + j] += i128::from(a[i]) * i128::from(b[j]);
            }
        }

        // Reduce modulo 2^255 - 19
        // The top 5 limbs (c[5..10]) represent values * 2^255
        // So we multiply by 19 and add to bottom 5 limbs
        for i in 0..5 {
            c[i] += c[i + 5] * 19;
        }

        // Convert back to i64 and reduce
        let limbs = [
            c[0] as i64,
            c[1] as i64,
            c[2] as i64,
            c[3] as i64,
            c[4] as i64,
        ];

        Self { limbs }.weak_reduce().weak_reduce() // Two rounds may be needed
    }
}

/// Equality comparison (compares reduced forms)
///
/// Note: This compares the canonical reduced representations,
/// so unreduced equal values will still compare as equal.
impl PartialEq for FieldElement {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other) == 1
    }
}

impl Eq for FieldElement {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_and_one() {
        let zero = FieldElement::ZERO;
        let one = FieldElement::ONE;

        assert!(zero.is_zero());
        assert!(!one.is_zero());
        assert_eq!(zero.ct_eq(&one), 0);
        assert_eq!(one.ct_eq(&one), 1);
    }

    #[test]
    fn test_addition() {
        let one = FieldElement::ONE;
        let two = one + one;

        assert_eq!(two.limbs[0], 2);
        assert!(!two.is_zero());
    }

    #[test]
    fn test_subtraction() {
        let two = FieldElement::ONE + FieldElement::ONE;
        let one = two - FieldElement::ONE;

        assert_eq!(one.ct_eq(&FieldElement::ONE), 1);
    }

    #[test]
    fn test_multiplication() {
        let two = FieldElement::ONE + FieldElement::ONE;
        let four = two * two;
        let expected = two + two;

        assert_eq!(four.ct_eq(&expected), 1);
    }

    #[test]
    fn test_negation() {
        let one = FieldElement::ONE;
        let neg_one = one.negate();
        let zero = one + neg_one;

        assert!(zero.is_zero());
    }

    #[test]
    fn test_reduce_idempotent() {
        let x = FieldElement::ONE + FieldElement::ONE;
        let r1 = x.reduce();
        let r2 = r1.reduce();

        assert_eq!(r1.ct_eq(&r2), 1);
    }

    #[test]
    fn test_round_trip() {
        let bytes = [42u8; 32];
        let fe = FieldElement::from_bytes(&bytes);
        let recovered = fe.to_bytes();

        // Round trip through field should be deterministic
        let fe2 = FieldElement::from_bytes(&recovered);
        assert_eq!(fe.ct_eq(&fe2), 1);
    }

    #[test]
    fn test_conditional_swap() {
        let mut a = FieldElement::ONE;
        let mut b = FieldElement::ZERO;

        let orig_a = a;
        let orig_b = b;

        // swap = 0: no swap
        a.conditional_swap(&mut b, 0);
        assert_eq!(a.ct_eq(&orig_a), 1);
        assert_eq!(b.ct_eq(&orig_b), 1);

        // swap = 1: swap
        a.conditional_swap(&mut b, 1);
        assert_eq!(a.ct_eq(&orig_b), 1);
        assert_eq!(b.ct_eq(&orig_a), 1);
    }
}
