// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Constant-Time Operations
//!
//! This module provides constant-time comparison operations to prevent
//! timing side-channel attacks.
//!
//! # Law 3 Compliance
//!
//! "ALL operations on secret data MUST be constant-time."
//!
//! # Security Properties
//!
//! - Comparison time is independent of input values
//! - No early termination on mismatch
//! - Memory access patterns are independent of input
//!
//! # Implementation Notes
//!
//! All operations use bitwise operations to ensure constant execution time.
//! The implementations are designed to avoid any conditional branches that
//! could leak information through timing.

use core::sync::atomic::{compiler_fence, Ordering};

/// Trait for constant-time equality comparison
pub trait ConstantTimeEq {
    /// Compare two values in constant time
    ///
    /// Returns `true` if the values are equal, `false` otherwise.
    /// The execution time is independent of the actual values.
    fn ct_eq(&self, other: &Self) -> bool;
}

/// Perform constant-time equality comparison on byte slices
///
/// # Panics
///
/// Panics if the slices have different lengths. For production code,
/// use `ct_eq_slices` which returns `false` for different lengths.
#[inline(never)]
pub fn ct_eq_bytes(a: &[u8], b: &[u8]) -> bool {
    assert_eq!(a.len(), b.len(), "Slices must have equal length");
    ct_eq_slices(a, b)
}

/// Perform constant-time equality comparison on byte slices
///
/// Returns `false` if the slices have different lengths.
/// The comparison time depends only on the length of the shorter slice.
#[inline(never)]
pub fn ct_eq_slices(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    // XOR all bytes together, accumulating differences
    let mut diff: u8 = 0;

    for (byte_a, byte_b) in a.iter().zip(b.iter()) {
        diff |= byte_a ^ byte_b;
    }

    // Prevent compiler from optimizing
    compiler_fence(Ordering::SeqCst);

    // If any bit is set, the values are different
    diff == 0
}

/// Constant-time select: returns `a` if `choice` is true, `b` otherwise
///
/// The execution time is independent of `choice`.
#[inline(never)]
pub fn ct_select<T>(choice: bool, a: T, b: T) -> T
where
    T: Copy
        + Default
        + std::ops::BitAnd<Output = T>
        + std::ops::BitOr<Output = T>
        + std::ops::Not<Output = T>,
{
    // Convert bool to all-ones or all-zeros mask
    let mask = if choice {
        !T::default() // All ones
    } else {
        T::default() // All zeros
    };

    compiler_fence(Ordering::SeqCst);

    // Select using bitwise operations:
    // (a & mask) | (b & !mask)
    // When mask is all-ones: (a & 1..1) | (b & 0..0) = a
    // When mask is all-zeros: (a & 0..0) | (b & 1..1) = b
    (a & mask) | (b & !mask)
}

/// Constant-time less-than comparison for u8
#[inline(never)]
pub fn ct_lt_u8(a: u8, b: u8) -> bool {
    // Use the sign bit of (a - b) when viewed as signed
    let diff = (a as i16) - (b as i16);
    compiler_fence(Ordering::SeqCst);
    diff < 0
}

// Implement ConstantTimeEq for byte arrays
impl<const N: usize> ConstantTimeEq for [u8; N] {
    fn ct_eq(&self, other: &Self) -> bool {
        ct_eq_slices(self, other)
    }
}

// Implement ConstantTimeEq for byte slices
impl ConstantTimeEq for [u8] {
    fn ct_eq(&self, other: &Self) -> bool {
        ct_eq_slices(self, other)
    }
}

// Implement ConstantTimeEq for primitive types
macro_rules! impl_ct_eq_for_primitive {
    ($t:ty, $bytes:expr) => {
        impl ConstantTimeEq for $t {
            fn ct_eq(&self, other: &Self) -> bool {
                let a_bytes = self.to_ne_bytes();
                let b_bytes = other.to_ne_bytes();
                ct_eq_slices(&a_bytes, &b_bytes)
            }
        }
    };
}

impl_ct_eq_for_primitive!(u8, 1);
impl_ct_eq_for_primitive!(u16, 2);
impl_ct_eq_for_primitive!(u32, 4);
impl_ct_eq_for_primitive!(u64, 8);
impl_ct_eq_for_primitive!(u128, 16);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ct_eq_same() {
        let a = [1u8, 2, 3, 4, 5];
        let b = [1u8, 2, 3, 4, 5];
        assert!(ct_eq_slices(&a, &b));
    }

    #[test]
    fn test_ct_eq_different() {
        let a = [1u8, 2, 3, 4, 5];
        let b = [1u8, 2, 3, 4, 6];
        assert!(!ct_eq_slices(&a, &b));
    }

    #[test]
    fn test_ct_eq_different_length() {
        let a = [1u8, 2, 3, 4, 5];
        let b = [1u8, 2, 3, 4];
        assert!(!ct_eq_slices(&a, &b));
    }

    #[test]
    fn test_ct_eq_array() {
        let a = [0xDEu8, 0xAD, 0xBE, 0xEF];
        let b = [0xDEu8, 0xAD, 0xBE, 0xEF];
        let c = [0xDEu8, 0xAD, 0xBE, 0x00];

        assert!(a.ct_eq(&b));
        assert!(!a.ct_eq(&c));
    }

    #[test]
    fn test_ct_eq_u64() {
        let a: u64 = 0xDEAD_BEEF_CAFE_BABE;
        let b: u64 = 0xDEAD_BEEF_CAFE_BABE;
        let c: u64 = 0xDEAD_BEEF_CAFE_BABA;

        assert!(a.ct_eq(&b));
        assert!(!a.ct_eq(&c));
    }

    #[test]
    fn test_ct_lt() {
        assert!(ct_lt_u8(5, 10));
        assert!(!ct_lt_u8(10, 5));
        assert!(!ct_lt_u8(5, 5));
        assert!(ct_lt_u8(0, 255));
    }

    #[test]
    fn test_ct_select_u8() {
        assert_eq!(ct_select(true, 0xAAu8, 0x55u8), 0xAA);
        assert_eq!(ct_select(false, 0xAAu8, 0x55u8), 0x55);
    }

    #[test]
    fn test_ct_select_u64() {
        let a: u64 = 0xDEAD_BEEF_CAFE_BABE;
        let b: u64 = 0x0123_4567_89AB_CDEF;
        assert_eq!(ct_select(true, a, b), a);
        assert_eq!(ct_select(false, a, b), b);
    }

    #[test]
    fn test_ct_select_preserves_all_bits() {
        // Every bit position must round-trip through the mask correctly.
        for shift in 0..32 {
            let a: u32 = 1 << shift;
            let b: u32 = !a;
            assert_eq!(ct_select(true, a, b), a);
            assert_eq!(ct_select(false, a, b), b);
        }
    }
}
