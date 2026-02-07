// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Secret Value Wrapper
//!
//! This module provides a wrapper type for secret values that ensures
//! automatic zeroization when the value goes out of scope.
//!
//! # Laws Enforced
//!
//! - **Law 3**: Constant-time comparison
//! - **Law 4**: Automatic zeroization on drop
//!
//! # Security Properties
//!
//! - Secret values are never printed in debug output
//! - Secret values are automatically zeroized when dropped
//! - Comparison operations are constant-time
//! - Access requires explicit method call

use crate::constant_time::ConstantTimeEq;
use crate::zeroize::Zeroize;
use core::fmt;

/// A wrapper for secret values that provides automatic zeroization
///
/// # Type Parameters
///
/// - `T`: The inner type, which must implement `Zeroize`
///
/// # Example
///
/// ```
/// use riina_core::secret::Secret;
///
/// // Create a secret key
/// let key = Secret::new([0x42u8; 32]);
///
/// // Access the secret when needed
/// let bytes = key.expose_secret();
/// assert_eq!(bytes[0], 0x42);
///
/// // Key is automatically zeroized when dropped
/// ```
pub struct Secret<T>
where
    T: Zeroize,
{
    /// The inner secret value
    inner: T,
}

impl<T> Secret<T>
where
    T: Zeroize,
{
    /// Create a new secret from a value
    ///
    /// The value will be automatically zeroized when the Secret is dropped.
    #[inline]
    pub fn new(value: T) -> Self {
        Self { inner: value }
    }

    /// Expose the secret value
    ///
    /// This method provides access to the inner value. Use with caution
    /// and ensure the value is not copied unnecessarily.
    ///
    /// # Security Note
    ///
    /// The returned reference should not be stored or copied. Access the
    /// secret only when absolutely necessary and for the minimum duration.
    #[inline]
    pub fn expose_secret(&self) -> &T {
        &self.inner
    }

    /// Expose the secret value mutably
    ///
    /// This method provides mutable access to the inner value.
    #[inline]
    pub fn expose_secret_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

// Implement Drop to ensure zeroization
impl<T> Drop for Secret<T>
where
    T: Zeroize,
{
    fn drop(&mut self) {
        self.inner.zeroize();
    }
}

// Implement Debug to prevent accidental exposure
impl<T> fmt::Debug for Secret<T>
where
    T: Zeroize,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("[REDACTED]")
    }
}

// Implement Clone only if the inner type is Clone
impl<T> Clone for Secret<T>
where
    T: Zeroize + Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

// Implement PartialEq using constant-time comparison
impl<T> PartialEq for Secret<T>
where
    T: Zeroize + ConstantTimeEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner.ct_eq(&other.inner)
    }
}

impl<T> Eq for Secret<T> where T: Zeroize + ConstantTimeEq {}

/// Type alias for a 32-byte secret (e.g., AES-256 key)
pub type Secret32 = Secret<[u8; 32]>;

/// Type alias for a 64-byte secret (e.g., two 256-bit keys)
pub type Secret64 = Secret<[u8; 64]>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_secret_debug() {
        let secret = Secret::new([0x42u8; 32]);
        let debug_str = format!("{:?}", secret);
        assert_eq!(debug_str, "[REDACTED]");
        assert!(!debug_str.contains("42"));
    }

    #[test]
    fn test_secret_expose() {
        let secret = Secret::new([0xABu8; 16]);
        let exposed = secret.expose_secret();
        assert!(exposed.iter().all(|&b| b == 0xAB));
    }

    #[test]
    fn test_secret_eq() {
        let a = Secret::new([1u8, 2, 3, 4]);
        let b = Secret::new([1u8, 2, 3, 4]);
        let c = Secret::new([1u8, 2, 3, 5]);

        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn test_secret_clone() {
        let original = Secret::new([0xFFu8; 8]);
        let cloned = original.clone();
        
        assert_eq!(original.expose_secret(), cloned.expose_secret());
    }
}
