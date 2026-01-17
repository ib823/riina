//! Secure Memory Zeroization
//!
//! This module provides secure zeroization of memory to ensure that
//! sensitive data does not persist in memory after it is no longer needed.
//!
//! # Law 4 Compliance
//!
//! "ALL secrets MUST be zeroized when no longer needed."
//!
//! # Security Properties
//!
//! - Zeroization is guaranteed to not be optimized away
//! - Uses volatile writes to prevent compiler optimization
//! - Works with any type that can be represented as bytes
//!
//! # Safety Note
//!
//! This module uses `unsafe` for volatile pointer writes. This is required
//! to prevent the compiler from optimizing away security-critical zeroization.
//! All unsafe usage is carefully audited and documented.

#![allow(unsafe_code)] // Required for volatile writes in zeroization

use core::ptr;
use core::sync::atomic::{compiler_fence, Ordering};

/// Trait for types that can be securely zeroized
pub trait Zeroize {
    /// Securely zero out the contents of this value
    fn zeroize(&mut self);
}

/// Zeroize a slice of bytes
///
/// This function uses volatile writes and compiler fences to ensure
/// the zeroization is not optimized away.
///
/// # Safety
///
/// This function is safe because it only writes zeros to valid memory.
#[inline(never)]
pub fn zeroize_slice(slice: &mut [u8]) {
    // Use volatile writes to prevent optimization
    for byte in slice.iter_mut() {
        // SAFETY: We're writing to valid, initialized memory
        // The pointer comes from a valid mutable reference
        // We're writing a valid u8 value (0)
        #[allow(clippy::ptr_cast_constness)]
        unsafe {
            ptr::write_volatile(byte as *mut u8, 0);
        }
    }
    
    // Memory barrier to ensure writes are not reordered
    compiler_fence(Ordering::SeqCst);
}

// Implement Zeroize for fixed-size arrays
impl<const N: usize> Zeroize for [u8; N] {
    fn zeroize(&mut self) {
        zeroize_slice(self);
    }
}

// Implement Zeroize for slices
impl Zeroize for [u8] {
    fn zeroize(&mut self) {
        zeroize_slice(self);
    }
}

// Implement Zeroize for Vec<u8>
impl Zeroize for Vec<u8> {
    fn zeroize(&mut self) {
        zeroize_slice(self.as_mut_slice());
        self.clear();
    }
}

// Implement Zeroize for primitive types
macro_rules! impl_zeroize_for_primitive {
    ($($t:ty),*) => {
        $(
            impl Zeroize for $t {
                fn zeroize(&mut self) {
                    // SAFETY: Writing zero to valid memory
                    #[allow(clippy::ptr_cast_constness)]
                    unsafe {
                        ptr::write_volatile(self as *mut $t, 0);
                    }
                    compiler_fence(Ordering::SeqCst);
                }
            }
        )*
    };
}

impl_zeroize_for_primitive!(u8, u16, u32, u64, u128, usize);
impl_zeroize_for_primitive!(i8, i16, i32, i64, i128, isize);

// Implement Zeroize for fixed-size arrays of u16
impl<const N: usize> Zeroize for [u16; N] {
    fn zeroize(&mut self) {
        for item in self.iter_mut() {
            item.zeroize();
        }
    }
}

// Implement Zeroize for fixed-size arrays of u32
impl<const N: usize> Zeroize for [u32; N] {
    fn zeroize(&mut self) {
        for item in self.iter_mut() {
            item.zeroize();
        }
    }
}

// Implement Zeroize for fixed-size arrays of u64
impl<const N: usize> Zeroize for [u64; N] {
    fn zeroize(&mut self) {
        for item in self.iter_mut() {
            item.zeroize();
        }
    }
}

// Implement Zeroize for fixed-size arrays of i16
impl<const N: usize> Zeroize for [i16; N] {
    fn zeroize(&mut self) {
        for item in self.iter_mut() {
            item.zeroize();
        }
    }
}

// Implement Zeroize for fixed-size arrays of i32
impl<const N: usize> Zeroize for [i32; N] {
    fn zeroize(&mut self) {
        for item in self.iter_mut() {
            item.zeroize();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zeroize_array() {
        let mut arr = [0xFFu8; 32];
        arr.zeroize();
        assert!(arr.iter().all(|&b| b == 0));
    }

    #[test]
    fn test_zeroize_vec() {
        let mut vec = vec![0xFFu8; 32];
        vec.zeroize();
        assert!(vec.is_empty());
    }

    #[test]
    fn test_zeroize_primitive() {
        let mut val: u64 = 0xDEAD_BEEF_CAFE_BABE;
        val.zeroize();
        assert_eq!(val, 0);
    }
}
