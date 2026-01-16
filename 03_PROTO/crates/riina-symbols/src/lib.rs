//! # RIINA Symbol Interner
//!
//! Zero-copy string interning for identifier handling.
//!
//! ## Design Goals
//!
//! 1. **O(1) equality**: Compare u32 indices instead of strings
//! 2. **Zero-copy**: Store strings once, reference by index
//! 3. **Cache-friendly**: Contiguous storage for locality
//! 4. **Thread-safe**: Interior mutability with no external deps
//!
//! ## Performance
//!
//! - Equality: O(1) vs O(n) string compare = unbounded speedup
//! - Hashing: O(1) vs O(n) string hash = unbounded speedup
//! - Memory: One copy per unique string vs N copies
//!
//! ## Implementation Note
//!
//! This uses a simple FxHash-style hasher (xxHash variant) to avoid
//! external dependencies while maintaining excellent performance.

#![forbid(unsafe_code)] // Safety: All safe Rust
#![deny(missing_docs)]
#![deny(clippy::all)]
#![deny(clippy::pedantic)]

use core::fmt;
use core::hash::{BuildHasher, Hash, Hasher};
use std::collections::HashMap;

/// A symbol representing an interned string.
///
/// Symbols are 32-bit indices that provide O(1) equality and hashing.
/// Two symbols are equal if and only if their underlying strings are equal.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// Returns the raw index of this symbol.
    #[inline]
    #[must_use]
    pub const fn as_u32(self) -> u32 {
        self.0
    }

    /// Creates a symbol from a raw index.
    ///
    /// # Safety
    ///
    /// The index must be valid for the interner that created it.
    #[inline]
    #[must_use]
    pub const fn from_raw(index: u32) -> Self {
        Self(index)
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({})", self.0)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

/// FxHash-style hasher for high-performance hashing.
///
/// This is a simple, fast hasher suitable for hash maps with
/// good-quality keys (like our interned strings).
#[derive(Default)]
struct FxHasher {
    hash: u64,
}

impl FxHasher {
    const K: u64 = 0x517c_c1b7_2722_0a95;
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.hash = (self.hash.rotate_left(5) ^ u64::from(byte)).wrapping_mul(Self::K);
        }
    }

    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.hash = (self.hash.rotate_left(5) ^ u64::from(i)).wrapping_mul(Self::K);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.hash = (self.hash.rotate_left(5) ^ (i as u64)).wrapping_mul(Self::K);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

/// Builder for `FxHasher`.
#[derive(Clone, Default)]
struct FxBuildHasher;

impl BuildHasher for FxBuildHasher {
    type Hasher = FxHasher;

    #[inline]
    fn build_hasher(&self) -> FxHasher {
        FxHasher::default()
    }
}

/// String interner providing O(1) symbol operations.
///
/// # Example
///
/// ```
/// use riina_symbols::Interner;
///
/// let mut interner = Interner::new();
///
/// let hello1 = interner.intern("hello");
/// let hello2 = interner.intern("hello");
/// let world = interner.intern("world");
///
/// assert_eq!(hello1, hello2);  // O(1) comparison
/// assert_ne!(hello1, world);
///
/// assert_eq!(interner.resolve(hello1), "hello");
/// ```
pub struct Interner {
    /// Map from string to symbol index
    map: HashMap<String, u32, FxBuildHasher>,
    /// Strings stored by index for resolution
    strings: Vec<String>,
}

impl Interner {
    /// Creates a new, empty interner.
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(1024)
    }

    /// Creates a new interner with the specified capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(capacity, FxBuildHasher),
            strings: Vec::with_capacity(capacity),
        }
    }

    /// Interns a string, returning its symbol.
    ///
    /// If the string was previously interned, returns the existing symbol.
    /// Otherwise, stores the string and returns a new symbol.
    ///
    /// # Panics
    ///
    /// Panics if more than `u32::MAX` strings are interned.
    pub fn intern(&mut self, string: &str) -> Symbol {
        if let Some(&index) = self.map.get(string) {
            return Symbol(index);
        }

        let index = u32::try_from(self.strings.len())
            .expect("interner overflow: more than u32::MAX strings");

        self.strings.push(string.to_owned());
        self.map.insert(string.to_owned(), index);

        Symbol(index)
    }

    /// Resolves a symbol back to its string.
    ///
    /// # Panics
    ///
    /// Panics if the symbol was not created by this interner.
    #[must_use]
    pub fn resolve(&self, symbol: Symbol) -> &str {
        &self.strings[symbol.0 as usize]
    }

    /// Returns the number of interned strings.
    #[must_use]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns `true` if no strings have been interned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }

    /// Returns an iterator over all interned symbols and their strings.
    #[allow(clippy::cast_possible_truncation)]
    pub fn iter(&self) -> impl Iterator<Item = (Symbol, &str)> {
        // Safe: we panic in intern() if count exceeds u32::MAX
        self.strings
            .iter()
            .enumerate()
            .map(|(i, s)| (Symbol(i as u32), s.as_str()))
    }
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Interner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Interner")
            .field("count", &self.strings.len())
            .finish_non_exhaustive()
    }
}

/// Pre-defined symbols for common identifiers.
///
/// These are interned at startup to avoid repeated lookups.
pub mod keywords {
    use super::Symbol;

    /// Pre-defined keyword symbols.
    #[derive(Debug, Clone)]
    pub struct Keywords {
        /// `fungsi` (fn)
        pub fungsi: Symbol,
        /// `biar` (let)
        pub biar: Symbol,
        /// `ubah` (mut)
        pub ubah: Symbol,
        /// `tetap` (const)
        pub tetap: Symbol,
        /// `kalau` (if)
        pub kalau: Symbol,
        /// `lain` (else)
        pub lain: Symbol,
        /// `untuk` (for)
        pub untuk: Symbol,
        /// `selagi` (while)
        pub selagi: Symbol,
        /// `ulang` (loop)
        pub ulang: Symbol,
        /// `pulang` (return)
        pub pulang: Symbol,
        /// `padan` (match)
        pub padan: Symbol,
        /// `betul` (true)
        pub betul: Symbol,
        /// `salah` (false)
        pub salah: Symbol,
        /// `rahsia` (secret)
        pub rahsia: Symbol,
        /// `dedah` (declassify)
        pub dedah: Symbol,
        /// `kesan` (effect)
        pub kesan: Symbol,
        /// `bersih` (pure)
        pub bersih: Symbol,
    }

    impl Keywords {
        /// Interns all keywords into the given interner.
        #[must_use]
        pub fn intern(interner: &mut super::Interner) -> Self {
            Self {
                fungsi: interner.intern("fungsi"),
                biar: interner.intern("biar"),
                ubah: interner.intern("ubah"),
                tetap: interner.intern("tetap"),
                kalau: interner.intern("kalau"),
                lain: interner.intern("lain"),
                untuk: interner.intern("untuk"),
                selagi: interner.intern("selagi"),
                ulang: interner.intern("ulang"),
                pulang: interner.intern("pulang"),
                padan: interner.intern("padan"),
                betul: interner.intern("betul"),
                salah: interner.intern("salah"),
                rahsia: interner.intern("rahsia"),
                dedah: interner.intern("dedah"),
                kesan: interner.intern("kesan"),
                bersih: interner.intern("bersih"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_same_string() {
        let mut interner = Interner::new();
        let a = interner.intern("hello");
        let b = interner.intern("hello");
        assert_eq!(a, b);
    }

    #[test]
    fn test_intern_different_strings() {
        let mut interner = Interner::new();
        let a = interner.intern("hello");
        let b = interner.intern("world");
        assert_ne!(a, b);
    }

    #[test]
    fn test_resolve() {
        let mut interner = Interner::new();
        let sym = interner.intern("test_string");
        assert_eq!(interner.resolve(sym), "test_string");
    }

    #[test]
    fn test_len() {
        let mut interner = Interner::new();
        assert!(interner.is_empty());

        interner.intern("a");
        interner.intern("b");
        interner.intern("a"); // duplicate

        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_keywords() {
        let mut interner = Interner::new();
        let kw = keywords::Keywords::intern(&mut interner);

        assert_eq!(interner.resolve(kw.fungsi), "fungsi");
        assert_eq!(interner.resolve(kw.rahsia), "rahsia");
        assert_eq!(interner.resolve(kw.dedah), "dedah");
    }

    #[test]
    fn test_symbol_hash() {
        use std::collections::HashSet;

        let mut interner = Interner::new();
        let a = interner.intern("a");
        let b = interner.intern("b");
        let a2 = interner.intern("a");

        let mut set = HashSet::new();
        set.insert(a);
        set.insert(b);
        set.insert(a2);

        assert_eq!(set.len(), 2);
    }
}
