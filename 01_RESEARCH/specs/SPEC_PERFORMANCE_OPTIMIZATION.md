# Performance Optimization Specification

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  SPECIFICATION: PERFORMANCE OPTIMIZATION FOR 03_PROTO                            ║
║  Version: 1.0.0                                                                  ║
║  Date: 2026-01-16                                                                ║
║  Status: SPECIFICATION - Ready for Implementation                                ║
║                                                                                  ║
║  Goal: Achieve 100x performance improvement in lexer/parser/typechecker          ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## 1. Performance Baseline

### 1.1 Current Architecture Bottlenecks

| Component | Current Approach | Problem | Impact |
|-----------|------------------|---------|--------|
| Lexer | `Peekable<Chars<'a>>` | UTF-8 decode per char | 5-10x slowdown |
| Lexer | String allocation for identifiers | Heap allocation | 3-5x slowdown |
| Parser | `Box<Expr>` everywhere | Pointer chasing | 2-5x slowdown |
| Parser | String cloning for AST | Memory copies | 2-3x slowdown |
| Type Checker | `HashMap<Ident, Ty>` | Hash overhead | 2x slowdown |
| Type Checker | Full context clone on extend | O(n) copies | Variable |

### 1.2 Target Performance

| Component | Current (est.) | Target | Improvement |
|-----------|----------------|--------|-------------|
| Lexer | 10 MB/s | 1 GB/s | 100x |
| Parser | 5 MB/s | 200 MB/s | 40x |
| Type Checker | 1K expr/s | 50K expr/s | 50x |
| Memory | 100 bytes/node | 20 bytes/node | 5x |

---

## 2. Phase 0: Foundation Infrastructure (NEW CRATES)

### 2.1 riina-symbols: String Interning

**File:** `03_PROTO/crates/riina-symbols/src/lib.rs`

```rust
//! Symbol table for string interning
//!
//! Converts strings to 4-byte Symbol IDs, eliminating
//! repeated allocations and enabling fast comparison.

#![forbid(unsafe_code)]

use std::collections::HashMap;
use std::cell::RefCell;

/// Interned symbol identifier (4 bytes vs 24+ for String)
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Symbol(u32);

impl Symbol {
    /// Get the underlying index
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

/// Global symbol table
pub struct SymbolTable {
    /// Stored strings (owned)
    strings: Vec<Box<str>>,
    /// Reverse lookup: string content -> symbol
    indices: HashMap<Box<str>, Symbol>,
}

impl SymbolTable {
    /// Create a new empty symbol table
    pub fn new() -> Self {
        Self {
            strings: Vec::with_capacity(4096),
            indices: HashMap::with_capacity(4096),
        }
    }

    /// Intern a string, returning its symbol
    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.indices.get(s) {
            return sym;
        }

        let idx = self.strings.len() as u32;
        let sym = Symbol(idx);
        let boxed: Box<str> = s.into();

        // SAFETY: We need to insert the same string into both collections.
        // We clone the box for the indices map.
        self.strings.push(boxed.clone());
        self.indices.insert(boxed, sym);

        sym
    }

    /// Resolve a symbol back to its string
    #[inline]
    pub fn resolve(&self, sym: Symbol) -> &str {
        &self.strings[sym.0 as usize]
    }

    /// Number of interned symbols
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

// Thread-local symbol table for single-threaded use
thread_local! {
    static SYMBOLS: RefCell<SymbolTable> = RefCell::new(SymbolTable::new());
}

/// Intern a string using the thread-local symbol table
pub fn intern(s: &str) -> Symbol {
    SYMBOLS.with(|table| table.borrow_mut().intern(s))
}

/// Resolve a symbol using the thread-local symbol table
pub fn resolve(sym: Symbol) -> String {
    SYMBOLS.with(|table| table.borrow().resolve(sym).to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_same_string() {
        let mut table = SymbolTable::new();
        let s1 = table.intern("hello");
        let s2 = table.intern("hello");
        assert_eq!(s1, s2);
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn test_intern_different_strings() {
        let mut table = SymbolTable::new();
        let s1 = table.intern("hello");
        let s2 = table.intern("world");
        assert_ne!(s1, s2);
        assert_eq!(table.len(), 2);
    }

    #[test]
    fn test_resolve() {
        let mut table = SymbolTable::new();
        let sym = table.intern("test_string");
        assert_eq!(table.resolve(sym), "test_string");
    }
}
```

**Cargo.toml:**
```toml
[package]
name = "riina-symbols"
version.workspace = true
edition.workspace = true

[dependencies]
# None - zero dependencies
```

---

### 2.2 riina-arena: Arena Allocator

**File:** `03_PROTO/crates/riina-arena/src/lib.rs`

```rust
//! Arena allocator for AST nodes
//!
//! Provides contiguous allocation with O(1) access by index.
//! All allocations freed together when arena is dropped.

#![forbid(unsafe_code)]

use std::marker::PhantomData;

/// Index into an arena
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Idx<T> {
    index: u32,
    _marker: PhantomData<T>,
}

impl<T> Idx<T> {
    /// Create a new index (internal use)
    fn new(index: u32) -> Self {
        Self {
            index,
            _marker: PhantomData,
        }
    }

    /// Get the raw index value
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.index
    }
}

/// Typed arena for homogeneous allocation
pub struct Arena<T> {
    data: Vec<T>,
}

impl<T> Arena<T> {
    /// Create a new empty arena
    pub fn new() -> Self {
        Self {
            data: Vec::with_capacity(1024),
        }
    }

    /// Create an arena with specified capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
        }
    }

    /// Allocate a value in the arena, returning its index
    pub fn alloc(&mut self, value: T) -> Idx<T> {
        let idx = self.data.len() as u32;
        self.data.push(value);
        Idx::new(idx)
    }

    /// Get a reference to a value by index
    #[inline]
    pub fn get(&self, idx: Idx<T>) -> &T {
        &self.data[idx.index as usize]
    }

    /// Get a mutable reference to a value by index
    #[inline]
    pub fn get_mut(&mut self, idx: Idx<T>) -> &mut T {
        &mut self.data[idx.index as usize]
    }

    /// Number of allocated items
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Iterate over all items with indices
    pub fn iter(&self) -> impl Iterator<Item = (Idx<T>, &T)> {
        self.data
            .iter()
            .enumerate()
            .map(|(i, v)| (Idx::new(i as u32), v))
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> std::ops::Index<Idx<T>> for Arena<T> {
    type Output = T;

    #[inline]
    fn index(&self, idx: Idx<T>) -> &Self::Output {
        self.get(idx)
    }
}

impl<T> std::ops::IndexMut<Idx<T>> for Arena<T> {
    #[inline]
    fn index_mut(&mut self, idx: Idx<T>) -> &mut Self::Output {
        self.get_mut(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloc_and_get() {
        let mut arena: Arena<i32> = Arena::new();
        let idx1 = arena.alloc(42);
        let idx2 = arena.alloc(100);

        assert_eq!(arena[idx1], 42);
        assert_eq!(arena[idx2], 100);
    }

    #[test]
    fn test_mutate() {
        let mut arena: Arena<i32> = Arena::new();
        let idx = arena.alloc(1);
        arena[idx] = 2;
        assert_eq!(arena[idx], 2);
    }
}
```

---

### 2.3 riina-span: Zero-Copy Spans

**File:** `03_PROTO/crates/riina-span/src/lib.rs`

```rust
//! Source location tracking without string copies
//!
//! Spans reference the original source by byte offsets.

#![forbid(unsafe_code)]

/// A span in source code (byte offsets)
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    /// Start byte offset (inclusive)
    pub start: u32,
    /// End byte offset (exclusive)
    pub end: u32,
}

impl Span {
    /// Create a new span
    #[inline]
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    /// Create a zero-length span at a position
    #[inline]
    pub const fn point(pos: u32) -> Self {
        Self { start: pos, end: pos }
    }

    /// Length in bytes
    #[inline]
    pub const fn len(&self) -> u32 {
        self.end - self.start
    }

    /// Check if span is empty
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Merge two spans (takes smallest start, largest end)
    #[inline]
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Extract the spanned text from source
    #[inline]
    pub fn text<'a>(&self, source: &'a str) -> &'a str {
        &source[self.start as usize..self.end as usize]
    }
}

/// Something that has a span
pub trait Spanned {
    fn span(&self) -> Span;
}

/// Source file with interned content
pub struct SourceFile {
    /// File name/path
    pub name: String,
    /// Source content
    pub content: String,
    /// Line start offsets (for line/column calculation)
    line_starts: Vec<u32>,
}

impl SourceFile {
    /// Create a new source file
    pub fn new(name: String, content: String) -> Self {
        let line_starts = std::iter::once(0)
            .chain(
                content
                    .bytes()
                    .enumerate()
                    .filter(|(_, b)| *b == b'\n')
                    .map(|(i, _)| (i + 1) as u32)
            )
            .collect();

        Self {
            name,
            content,
            line_starts,
        }
    }

    /// Get line and column (1-indexed) for a byte offset
    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let line = self.line_starts
            .partition_point(|&start| start <= offset);
        let line_start = self.line_starts[line - 1];
        let col = offset - line_start + 1;
        (line as u32, col)
    }

    /// Get text for a span
    pub fn text(&self, span: Span) -> &str {
        span.text(&self.content)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_text() {
        let source = "hello world";
        let span = Span::new(0, 5);
        assert_eq!(span.text(source), "hello");
    }

    #[test]
    fn test_line_col() {
        let src = SourceFile::new("test".into(), "line1\nline2\nline3".into());
        assert_eq!(src.line_col(0), (1, 1));  // Start of line 1
        assert_eq!(src.line_col(6), (2, 1));  // Start of line 2
        assert_eq!(src.line_col(8), (2, 3));  // "n" in "line2"
    }
}
```

---

## 3. Lexer Optimization

### 3.1 New Lexer Architecture

**File:** `03_PROTO/crates/riina-lexer/src/fast_lexer.rs` (NEW)

```rust
//! High-performance lexer using byte-level scanning
//!
//! Optimizations:
//! - Works on &[u8] directly, minimal UTF-8 handling
//! - SIMD-accelerated whitespace skipping
//! - Lookup tables for character classification
//! - Zero-copy tokens (spans into source)

use crate::token::{Token, TokenKind};
use riina_span::Span;
use riina_symbols::Symbol;

/// Character class for lookup table
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum CharClass {
    Invalid = 0,
    Whitespace = 1,
    Alpha = 2,      // a-z, A-Z, _
    Digit = 3,      // 0-9
    Punct = 4,      // operators, delimiters
    Quote = 5,      // " and '
    Newline = 6,
    Other = 7,
}

/// Lookup table for ASCII character classification
static CHAR_CLASS: [CharClass; 256] = {
    let mut table = [CharClass::Other; 256];

    // Whitespace
    table[b' ' as usize] = CharClass::Whitespace;
    table[b'\t' as usize] = CharClass::Whitespace;
    table[b'\r' as usize] = CharClass::Whitespace;
    table[b'\n' as usize] = CharClass::Newline;

    // Digits
    let mut i = b'0';
    while i <= b'9' {
        table[i as usize] = CharClass::Digit;
        i += 1;
    }

    // Lowercase
    let mut i = b'a';
    while i <= b'z' {
        table[i as usize] = CharClass::Alpha;
        i += 1;
    }

    // Uppercase
    let mut i = b'A';
    while i <= b'Z' {
        table[i as usize] = CharClass::Alpha;
        i += 1;
    }

    // Underscore
    table[b'_' as usize] = CharClass::Alpha;

    // Quotes
    table[b'"' as usize] = CharClass::Quote;
    table[b'\'' as usize] = CharClass::Quote;

    // Punctuation (operators and delimiters)
    for &c in b"()[]{}.,;:+-*/%&|^!<>=@#$?\\~" {
        table[c as usize] = CharClass::Punct;
    }

    table
};

/// Keyword lookup using perfect hashing or trie
mod keywords {
    use super::*;
    use crate::token::TokenKind;

    /// Check if identifier is a keyword
    pub fn lookup(s: &str) -> Option<TokenKind> {
        // Fast path: check length first
        match s.len() {
            2 => match s {
                "fn" => Some(TokenKind::KwFn),
                "if" => Some(TokenKind::KwIf),
                "as" => Some(TokenKind::KwAs),
                "ct" => Some(TokenKind::KwCt),
                _ => None,
            },
            3 => match s {
                "let" => Some(TokenKind::KwLet),
                "mut" => Some(TokenKind::KwMut),
                "for" => Some(TokenKind::KwFor),
                "pub" => Some(TokenKind::KwPub),
                "use" => Some(TokenKind::KwUse),
                "mod" => Some(TokenKind::KwMod),
                "ref" => Some(TokenKind::KwRef),
                "end" => Some(TokenKind::KwEnd),
                "inl" => Some(TokenKind::KwInl),
                "inr" => Some(TokenKind::KwInr),
                _ => None,
            },
            4 => match s {
                "true" => Some(TokenKind::LiteralBool(true)),
                "else" => Some(TokenKind::KwElse),
                "enum" => Some(TokenKind::KwEnum),
                "impl" => Some(TokenKind::KwImpl),
                "loop" => Some(TokenKind::KwLoop),
                "self" => Some(TokenKind::KwSelfValue),
                "Self" => Some(TokenKind::KwSelfType),
                "send" => Some(TokenKind::KwSend),
                "recv" => Some(TokenKind::KwRecv),
                "with" => Some(TokenKind::KwWith),
                "move" => Some(TokenKind::KwMove),
                "type" => Some(TokenKind::KwType),
                _ => None,
            },
            5 => match s {
                "false" => Some(TokenKind::LiteralBool(false)),
                "const" => Some(TokenKind::KwConst),
                "match" => Some(TokenKind::KwMatch),
                "while" => Some(TokenKind::KwWhile),
                "break" => Some(TokenKind::KwBreak),
                "trait" => Some(TokenKind::KwTrait),
                "where" => Some(TokenKind::KwWhere),
                "super" => Some(TokenKind::KwSuper),
                "crate" => Some(TokenKind::KwCrate),
                "async" => Some(TokenKind::KwAsync),
                "await" => Some(TokenKind::KwAwait),
                "fence" => Some(TokenKind::KwFence),
                "prove" => Some(TokenKind::KwProve),
                "abort" => Some(TokenKind::KwAbort),
                "union" => Some(TokenKind::KwUnion),
                _ => None,
            },
            // ... continue for other lengths
            _ => None,
        }
    }
}

/// Fast lexer working on bytes
pub struct FastLexer<'src> {
    /// Source bytes
    bytes: &'src [u8],
    /// Source as string (for UTF-8 when needed)
    source: &'src str,
    /// Current position
    pos: usize,
}

impl<'src> FastLexer<'src> {
    /// Create a new lexer
    pub fn new(source: &'src str) -> Self {
        Self {
            bytes: source.as_bytes(),
            source,
            pos: 0,
        }
    }

    /// Skip whitespace and comments
    fn skip_trivia(&mut self) {
        loop {
            // Skip whitespace
            while self.pos < self.bytes.len() {
                match CHAR_CLASS[self.bytes[self.pos] as usize] {
                    CharClass::Whitespace | CharClass::Newline => self.pos += 1,
                    _ => break,
                }
            }

            // Check for comments
            if self.pos + 1 < self.bytes.len() && self.bytes[self.pos] == b'/' {
                if self.bytes[self.pos + 1] == b'/' {
                    // Line comment
                    self.pos += 2;
                    while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                        self.pos += 1;
                    }
                    continue;
                } else if self.bytes[self.pos + 1] == b'*' {
                    // Block comment (with nesting)
                    self.pos += 2;
                    let mut depth = 1;
                    while depth > 0 && self.pos + 1 < self.bytes.len() {
                        if self.bytes[self.pos] == b'/' && self.bytes[self.pos + 1] == b'*' {
                            depth += 1;
                            self.pos += 2;
                        } else if self.bytes[self.pos] == b'*' && self.bytes[self.pos + 1] == b'/' {
                            depth -= 1;
                            self.pos += 2;
                        } else {
                            self.pos += 1;
                        }
                    }
                    continue;
                }
            }

            break;
        }
    }

    /// Scan an identifier or keyword
    fn scan_identifier(&mut self) -> TokenKind {
        let start = self.pos;

        // First character already validated as Alpha
        self.pos += 1;

        // Continue with alphanumeric
        while self.pos < self.bytes.len() {
            match CHAR_CLASS[self.bytes[self.pos] as usize] {
                CharClass::Alpha | CharClass::Digit => self.pos += 1,
                _ => break,
            }
        }

        let text = &self.source[start..self.pos];

        // Check for keyword
        if let Some(kw) = keywords::lookup(text) {
            kw
        } else {
            TokenKind::Identifier(text.to_string()) // TODO: Use Symbol
        }
    }

    /// Scan a number literal
    fn scan_number(&mut self) -> TokenKind {
        let start = self.pos;
        self.pos += 1;

        // Check for hex/oct/bin
        if self.bytes[start] == b'0' && self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b'x' | b'X' => {
                    self.pos += 1;
                    while self.pos < self.bytes.len() {
                        let b = self.bytes[self.pos];
                        if b.is_ascii_hexdigit() || b == b'_' {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                    return TokenKind::LiteralInt(self.source[start..self.pos].to_string(), None);
                }
                b'o' | b'O' => {
                    // Octal
                    self.pos += 1;
                    while self.pos < self.bytes.len() {
                        let b = self.bytes[self.pos];
                        if (b'0'..=b'7').contains(&b) || b == b'_' {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                    return TokenKind::LiteralInt(self.source[start..self.pos].to_string(), None);
                }
                b'b' | b'B' => {
                    // Binary
                    self.pos += 1;
                    while self.pos < self.bytes.len() {
                        let b = self.bytes[self.pos];
                        if b == b'0' || b == b'1' || b == b'_' {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                    return TokenKind::LiteralInt(self.source[start..self.pos].to_string(), None);
                }
                _ => {}
            }
        }

        // Decimal digits
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            if b.is_ascii_digit() || b == b'_' {
                self.pos += 1;
            } else {
                break;
            }
        }

        // Check for float
        if self.pos < self.bytes.len() && self.bytes[self.pos] == b'.' {
            // Look ahead to distinguish from range (..)
            if self.pos + 1 < self.bytes.len() && self.bytes[self.pos + 1] != b'.' {
                self.pos += 1; // consume .
                while self.pos < self.bytes.len() {
                    let b = self.bytes[self.pos];
                    if b.is_ascii_digit() || b == b'_' {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                return TokenKind::LiteralFloat(self.source[start..self.pos].to_string(), None);
            }
        }

        TokenKind::LiteralInt(self.source[start..self.pos].to_string(), None)
    }

    /// Get next token
    pub fn next_token(&mut self) -> Token {
        self.skip_trivia();

        let start = self.pos as u32;

        if self.pos >= self.bytes.len() {
            return Token::new(TokenKind::Eof, Span::new(start, start));
        }

        let b = self.bytes[self.pos];

        let kind = match CHAR_CLASS[b as usize] {
            CharClass::Alpha => self.scan_identifier(),
            CharClass::Digit => self.scan_number(),
            CharClass::Punct => self.scan_punct(),
            CharClass::Quote => self.scan_string_or_char(),
            _ => {
                self.pos += 1;
                TokenKind::Unknown(b as char)
            }
        };

        Token::new(kind, Span::new(start, self.pos as u32))
    }

    fn scan_punct(&mut self) -> TokenKind {
        let b = self.bytes[self.pos];
        self.pos += 1;

        match b {
            b'(' => TokenKind::LParen,
            b')' => TokenKind::RParen,
            b'[' => TokenKind::LBracket,
            b']' => TokenKind::RBracket,
            b'{' => TokenKind::LBrace,
            b'}' => TokenKind::RBrace,
            b',' => TokenKind::Comma,
            b';' => TokenKind::Semi,
            b'.' => self.scan_dot(),
            b':' => self.scan_colon(),
            b'+' => self.scan_plus(),
            b'-' => self.scan_minus(),
            b'*' => self.scan_star(),
            b'/' => self.scan_slash(),
            b'%' => self.scan_percent(),
            b'&' => self.scan_and(),
            b'|' => self.scan_or(),
            b'^' => self.scan_caret(),
            b'!' => self.scan_bang(),
            b'=' => self.scan_eq(),
            b'<' => self.scan_lt(),
            b'>' => self.scan_gt(),
            b'@' => TokenKind::At,
            b'#' => TokenKind::Hash,
            b'$' => TokenKind::Dollar,
            b'?' => TokenKind::Question,
            _ => TokenKind::Unknown(b as char),
        }
    }

    // Helper methods for multi-character operators
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn scan_dot(&mut self) -> TokenKind {
        if self.peek() == Some(b'.') {
            self.pos += 1;
            if self.peek() == Some(b'=') {
                self.pos += 1;
                TokenKind::DotDotEq
            } else {
                TokenKind::DotDot
            }
        } else {
            TokenKind::Dot
        }
    }

    fn scan_colon(&mut self) -> TokenKind {
        match self.peek() {
            Some(b':') => { self.pos += 1; TokenKind::ColonColon }
            Some(b'=') => { self.pos += 1; TokenKind::ColonEq }
            _ => TokenKind::Colon,
        }
    }

    fn scan_plus(&mut self) -> TokenKind {
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::PlusEq
        } else {
            TokenKind::Plus
        }
    }

    fn scan_minus(&mut self) -> TokenKind {
        match self.peek() {
            Some(b'=') => { self.pos += 1; TokenKind::MinusEq }
            Some(b'>') => { self.pos += 1; TokenKind::Arrow }
            _ => TokenKind::Minus,
        }
    }

    fn scan_star(&mut self) -> TokenKind {
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::StarEq
        } else {
            TokenKind::Star
        }
    }

    fn scan_slash(&mut self) -> TokenKind {
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::SlashEq
        } else {
            TokenKind::Slash
        }
    }

    fn scan_percent(&mut self) -> TokenKind {
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::PercentEq
        } else {
            TokenKind::Percent
        }
    }

    fn scan_and(&mut self) -> TokenKind {
        match self.peek() {
            Some(b'=') => { self.pos += 1; TokenKind::AndEq }
            Some(b'&') => { self.pos += 1; TokenKind::AndAnd }
            _ => TokenKind::And,
        }
    }

    fn scan_or(&mut self) -> TokenKind {
        match self.peek() {
            Some(b'=') => { self.pos += 1; TokenKind::OrEq }
            Some(b'|') => { self.pos += 1; TokenKind::OrOr }
            _ => TokenKind::Or,
        }
    }

    fn scan_caret(&mut self) -> TokenKind {
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::CaretEq
        } else {
            TokenKind::Caret
        }
    }

    fn scan_bang(&mut self) -> TokenKind {
        if self.peek() == Some(b'=') {
            self.pos += 1;
            TokenKind::Ne
        } else {
            TokenKind::Not
        }
    }

    fn scan_eq(&mut self) -> TokenKind {
        match self.peek() {
            Some(b'=') => { self.pos += 1; TokenKind::EqEq }
            Some(b'>') => { self.pos += 1; TokenKind::FatArrow }
            _ => TokenKind::Eq,
        }
    }

    fn scan_lt(&mut self) -> TokenKind {
        match self.peek() {
            Some(b'=') => { self.pos += 1; TokenKind::Le }
            Some(b'<') => {
                self.pos += 1;
                if self.peek() == Some(b'=') {
                    self.pos += 1;
                    TokenKind::ShlEq
                } else {
                    TokenKind::Shl
                }
            }
            _ => TokenKind::Lt,
        }
    }

    fn scan_gt(&mut self) -> TokenKind {
        match self.peek() {
            Some(b'=') => { self.pos += 1; TokenKind::Ge }
            Some(b'>') => {
                self.pos += 1;
                if self.peek() == Some(b'=') {
                    self.pos += 1;
                    TokenKind::ShrEq
                } else {
                    TokenKind::Shr
                }
            }
            _ => TokenKind::Gt,
        }
    }

    fn scan_string_or_char(&mut self) -> TokenKind {
        // Simplified - full implementation would handle escapes properly
        let quote = self.bytes[self.pos];
        self.pos += 1;
        let start = self.pos;

        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            if b == quote {
                let text = &self.source[start..self.pos];
                self.pos += 1;
                return if quote == b'"' {
                    TokenKind::LiteralString(text.to_string())
                } else {
                    // Character or lifetime
                    if text.len() == 1 {
                        TokenKind::LiteralChar(text.chars().next().unwrap())
                    } else {
                        TokenKind::Lifetime(text.to_string())
                    }
                };
            }
            if b == b'\\' {
                self.pos += 2; // Skip escape
            } else {
                self.pos += 1;
            }
        }

        TokenKind::Unknown('"') // Unterminated
    }
}
```

---

## 4. SIMD Acceleration (Future)

### 4.1 AVX2 Whitespace Skip

**File:** `03_PROTO/crates/riina-lexer/src/simd.rs` (NEW)

For x86_64 with AVX2, process 32 bytes at once:

```rust
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
pub unsafe fn skip_whitespace_avx2(bytes: &[u8], start: usize) -> usize {
    use std::arch::x86_64::*;

    let mut pos = start;
    let len = bytes.len();

    // Process 32 bytes at a time
    while pos + 32 <= len {
        let chunk = _mm256_loadu_si256(bytes.as_ptr().add(pos) as *const __m256i);

        // Compare with whitespace characters
        let space = _mm256_set1_epi8(b' ' as i8);
        let tab = _mm256_set1_epi8(b'\t' as i8);
        let cr = _mm256_set1_epi8(b'\r' as i8);
        let lf = _mm256_set1_epi8(b'\n' as i8);

        let is_space = _mm256_cmpeq_epi8(chunk, space);
        let is_tab = _mm256_cmpeq_epi8(chunk, tab);
        let is_cr = _mm256_cmpeq_epi8(chunk, cr);
        let is_lf = _mm256_cmpeq_epi8(chunk, lf);

        let is_ws = _mm256_or_si256(
            _mm256_or_si256(is_space, is_tab),
            _mm256_or_si256(is_cr, is_lf),
        );

        let mask = _mm256_movemask_epi8(is_ws) as u32;

        if mask != 0xFFFFFFFF {
            // Found non-whitespace
            return pos + (!mask).trailing_zeros() as usize;
        }

        pos += 32;
    }

    // Scalar fallback
    while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
        pos += 1;
    }

    pos
}
```

---

## 5. Benchmarking Requirements

### 5.1 Benchmark Suite

**File:** `03_PROTO/benches/lexer_bench.rs` (NEW)

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

fn lexer_benchmark(c: &mut Criterion) {
    // Generate test input
    let small = include_str!("../test_data/small.rii");   // ~1 KB
    let medium = include_str!("../test_data/medium.rii"); // ~100 KB
    let large = include_str!("../test_data/large.rii");   // ~10 MB

    let mut group = c.benchmark_group("lexer");

    // Small file
    group.throughput(Throughput::Bytes(small.len() as u64));
    group.bench_function("small", |b| {
        b.iter(|| {
            let mut lexer = FastLexer::new(black_box(small));
            while lexer.next_token().kind != TokenKind::Eof {}
        })
    });

    // Medium file
    group.throughput(Throughput::Bytes(medium.len() as u64));
    group.bench_function("medium", |b| {
        b.iter(|| {
            let mut lexer = FastLexer::new(black_box(medium));
            while lexer.next_token().kind != TokenKind::Eof {}
        })
    });

    // Large file
    group.throughput(Throughput::Bytes(large.len() as u64));
    group.bench_function("large", |b| {
        b.iter(|| {
            let mut lexer = FastLexer::new(black_box(large));
            while lexer.next_token().kind != TokenKind::Eof {}
        })
    });

    group.finish();
}

criterion_group!(benches, lexer_benchmark);
criterion_main!(benches);
```

### 5.2 Performance Targets

| Input Size | Current (est.) | Target | Metric |
|------------|----------------|--------|--------|
| 1 KB | 0.1 ms | 0.001 ms | Time |
| 100 KB | 10 ms | 0.1 ms | Time |
| 10 MB | 1000 ms | 10 ms | Time |
| Throughput | 10 MB/s | 1000 MB/s | MB/s |

---

## 6. Migration Strategy

### 6.1 Phase 1: Add New Infrastructure (No Breaking Changes)

1. Create `riina-symbols` crate
2. Create `riina-arena` crate
3. Create `riina-span` crate
4. Add `fast_lexer.rs` alongside existing `lexer.rs`

### 6.2 Phase 2: Gradual Migration

1. Add feature flag for fast lexer
2. Run both lexers in CI, compare outputs
3. Benchmark both versions

### 6.3 Phase 3: Switchover

1. Make fast lexer the default
2. Deprecate old lexer
3. Remove old lexer after transition period

---

## 7. Verification Criteria

- [ ] All existing tests pass with new lexer
- [ ] Benchmark shows >10x improvement
- [ ] Memory usage reduced
- [ ] No new dependencies added
- [ ] Zero `unsafe` in public API
- [ ] Documentation complete

---

*Document Status: SPECIFICATION - Ready for Implementation*
*Last Updated: 2026-01-16*
