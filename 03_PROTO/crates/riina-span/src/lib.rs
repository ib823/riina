// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! # RIINA Source Spans
//!
//! Efficient source location tracking with 8-byte packed spans.
//!
//! ## Design Goals
//!
//! 1. **Compact**: 8 bytes per span (fits in a register)
//! 2. **Fast access**: Direct field access, no indirection
//! 3. **Error reporting**: Full line/column information on demand
//! 4. **Multi-file**: Support for multiple source files
//!
//! ## Memory Layout
//!
//! ```text
//! Span (8 bytes):
//! ┌────────────────┬────────────────┐
//! │ start (u32)    │ end (u32)      │
//! └────────────────┴────────────────┘
//!
//! FileId: u16 (supports 65,536 files)
//! BytePos: u32 (supports 4GB files)
//! ```
//!
//! ## Usage
//!
//! ```
//! use riina_span::{Span, SourceMap, FileId};
//!
//! let mut source_map = SourceMap::new();
//! let file_id = source_map.add_file("main.rii", "fungsi utama() { }");
//!
//! let span = Span::new(0, 6); // "fungsi"
//! let loc = source_map.lookup(file_id, span.start());
//!
//! assert_eq!(loc.line, 1);
//! assert_eq!(loc.column, 1);
//! ```

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(clippy::all)]
#![deny(clippy::pedantic)]

use core::fmt;
use core::ops::Range;

/// A byte position in a source file.
pub type BytePos = u32;

/// A file identifier.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FileId(u16);

impl FileId {
    /// Creates a new file ID from a raw value.
    #[inline]
    #[must_use]
    pub const fn new(id: u16) -> Self {
        Self(id)
    }

    /// Returns the raw file ID value.
    #[inline]
    #[must_use]
    pub const fn as_u16(self) -> u16 {
        self.0
    }
}

/// A span of source code.
///
/// This is an 8-byte value containing start and end byte positions.
/// The span is inclusive of `start` and exclusive of `end` (half-open interval).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// Start byte position (inclusive)
    start: BytePos,
    /// End byte position (exclusive)
    end: BytePos,
}

impl Span {
    /// A dummy span for synthetic nodes.
    pub const DUMMY: Self = Self { start: 0, end: 0 };

    /// Creates a new span from start and end positions.
    #[inline]
    #[must_use]
    pub const fn new(start: BytePos, end: BytePos) -> Self {
        Self { start, end }
    }

    /// Creates a span from a range.
    #[inline]
    #[must_use]
    #[allow(clippy::cast_possible_truncation)]
    pub fn from_range(range: Range<usize>) -> Self {
        // Note: We truncate to u32. Files > 4GB are not supported.
        Self {
            start: range.start as BytePos,
            end: range.end as BytePos,
        }
    }

    /// Returns the start position.
    #[inline]
    #[must_use]
    pub const fn start(self) -> BytePos {
        self.start
    }

    /// Returns the end position.
    #[inline]
    #[must_use]
    pub const fn end(self) -> BytePos {
        self.end
    }

    /// Returns the length in bytes.
    #[inline]
    #[must_use]
    pub const fn len(self) -> u32 {
        self.end.saturating_sub(self.start)
    }

    /// Returns `true` if this is an empty span.
    #[inline]
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start >= self.end
    }

    /// Returns `true` if this is a dummy span.
    #[inline]
    #[must_use]
    pub const fn is_dummy(self) -> bool {
        self.start == 0 && self.end == 0
    }

    /// Creates a span covering both this span and another.
    #[inline]
    #[must_use]
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Returns `true` if this span contains the given position.
    #[inline]
    #[must_use]
    pub const fn contains(self, pos: BytePos) -> bool {
        pos >= self.start && pos < self.end
    }

    /// Converts to a byte range.
    #[inline]
    #[must_use]
    pub fn to_range(self) -> Range<usize> {
        (self.start as usize)..(self.end as usize)
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self::from_range(range)
    }
}

/// A source location with line and column information.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SourceLocation {
    /// Line number (1-indexed)
    pub line: u32,
    /// Column number (1-indexed, in bytes)
    pub column: u32,
    /// Byte offset from start of file
    pub offset: BytePos,
}

impl SourceLocation {
    /// Creates a new source location.
    #[must_use]
    pub const fn new(line: u32, column: u32, offset: BytePos) -> Self {
        Self { line, column, offset }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// A source file with line information.
#[derive(Debug)]
pub struct SourceFile {
    /// File name (path or synthetic name)
    name: String,
    /// Source code content
    source: String,
    /// Byte offsets of line starts
    line_starts: Vec<BytePos>,
}

impl SourceFile {
    /// Creates a new source file.
    #[must_use]
    pub fn new(name: impl Into<String>, source: impl Into<String>) -> Self {
        let source = source.into();
        let line_starts = Self::compute_line_starts(&source);
        Self {
            name: name.into(),
            source,
            line_starts,
        }
    }

    /// Computes line start offsets.
    #[allow(clippy::cast_possible_truncation)]
    fn compute_line_starts(source: &str) -> Vec<BytePos> {
        let mut starts = vec![0];
        for (i, c) in source.char_indices() {
            if c == '\n' {
                // Note: We truncate to u32. Files > 4GB are not supported.
                starts.push((i + 1) as BytePos);
            }
        }
        starts
    }

    /// Returns the file name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the source code.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Returns the number of lines.
    #[must_use]
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    /// Looks up the line and column for a byte position.
    #[must_use]
    #[allow(clippy::cast_possible_truncation)]
    pub fn lookup(&self, pos: BytePos) -> SourceLocation {
        let line = match self.line_starts.binary_search(&pos) {
            Ok(line) => line,
            Err(line) => line.saturating_sub(1),
        };

        let line_start = self.line_starts[line];
        let column = pos.saturating_sub(line_start) + 1;

        // Note: We truncate to u32. Files with > 4B lines are not supported.
        SourceLocation {
            line: (line + 1) as u32,
            column,
            offset: pos,
        }
    }

    /// Returns the source text for a span.
    #[must_use]
    pub fn span_text(&self, span: Span) -> &str {
        let start = span.start as usize;
        let end = span.end as usize;
        self.source.get(start..end).unwrap_or("")
    }

    /// Returns the line text for a given line number (1-indexed).
    #[must_use]
    pub fn line_text(&self, line: u32) -> &str {
        let line_idx = (line as usize).saturating_sub(1);
        if line_idx >= self.line_starts.len() {
            return "";
        }

        let start = self.line_starts[line_idx] as usize;
        let end = self
            .line_starts
            .get(line_idx + 1)
            .map_or(self.source.len(), |&pos| pos as usize);

        self.source
            .get(start..end)
            .map_or("", |s| s.trim_end_matches('\n'))
    }
}

/// A source map containing multiple files.
#[derive(Debug, Default)]
pub struct SourceMap {
    /// All source files
    files: Vec<SourceFile>,
}

impl SourceMap {
    /// Creates a new, empty source map.
    #[must_use]
    pub fn new() -> Self {
        Self { files: Vec::new() }
    }

    /// Adds a file to the source map, returning its ID.
    ///
    /// # Panics
    ///
    /// Panics if more than `u16::MAX` files are added.
    pub fn add_file(&mut self, name: impl Into<String>, source: impl Into<String>) -> FileId {
        let id = u16::try_from(self.files.len())
            .expect("source map overflow: more than u16::MAX files");

        self.files.push(SourceFile::new(name, source));
        FileId(id)
    }

    /// Returns a reference to a source file by ID.
    ///
    /// # Panics
    ///
    /// Panics if the file ID is invalid.
    #[must_use]
    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    /// Looks up a source location.
    #[must_use]
    pub fn lookup(&self, file: FileId, pos: BytePos) -> SourceLocation {
        self.file(file).lookup(pos)
    }

    /// Returns a reference to a source file by ID, or `None` if invalid.
    #[must_use]
    pub fn get_file(&self, id: FileId) -> Option<&SourceFile> {
        self.files.get(id.0 as usize)
    }

    /// Returns the number of files.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.files.len()
    }
}

/// A span annotated with its file ID.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FullSpan {
    /// The file this span belongs to
    pub file: FileId,
    /// The span within the file
    pub span: Span,
}

impl FullSpan {
    /// Creates a new full span.
    #[must_use]
    pub const fn new(file: FileId, span: Span) -> Self {
        Self { file, span }
    }
}

/// A spanned value (value + location).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Spanned<T> {
    /// The value
    pub value: T,
    /// The source span
    pub span: Span,
}

impl<T> Spanned<T> {
    /// Creates a new spanned value.
    #[must_use]
    pub const fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }

    /// Maps the value while preserving the span.
    #[must_use]
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Spanned<U> {
        Spanned {
            value: f(self.value),
            span: self.span,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} @ {:?}", self.value, self.span)
    }
}

/// Bilingual diagnostic rendering.
pub mod diagnostics;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_basics() {
        let span = Span::new(10, 20);
        assert_eq!(span.start(), 10);
        assert_eq!(span.end(), 20);
        assert_eq!(span.len(), 10);
        assert!(!span.is_empty());
    }

    #[test]
    fn test_span_contains() {
        let span = Span::new(10, 20);
        assert!(!span.contains(9));
        assert!(span.contains(10));
        assert!(span.contains(15));
        assert!(span.contains(19));
        assert!(!span.contains(20));
    }

    #[test]
    fn test_span_merge() {
        let a = Span::new(10, 20);
        let b = Span::new(15, 30);
        let merged = a.merge(b);
        assert_eq!(merged.start(), 10);
        assert_eq!(merged.end(), 30);
    }

    #[test]
    fn test_source_file_lookup() {
        let file = SourceFile::new("test.rii", "abc\ndef\nghi");
        // "abc\ndef\nghi"
        //  0123 4567 89...
        //  L1   L2   L3

        let loc1 = file.lookup(0);
        assert_eq!(loc1.line, 1);
        assert_eq!(loc1.column, 1);

        let loc2 = file.lookup(4);
        assert_eq!(loc2.line, 2);
        assert_eq!(loc2.column, 1);

        let loc3 = file.lookup(6);
        assert_eq!(loc3.line, 2);
        assert_eq!(loc3.column, 3);

        let loc4 = file.lookup(8);
        assert_eq!(loc4.line, 3);
        assert_eq!(loc4.column, 1);
    }

    #[test]
    fn test_source_file_line_text() {
        let file = SourceFile::new("test.rii", "fungsi utama() {\n    pulang 0;\n}");

        assert_eq!(file.line_text(1), "fungsi utama() {");
        assert_eq!(file.line_text(2), "    pulang 0;");
        assert_eq!(file.line_text(3), "}");
        assert_eq!(file.line_text(4), "");
    }

    #[test]
    fn test_source_file_span_text() {
        let file = SourceFile::new("test.rii", "fungsi utama()");
        let span = Span::new(0, 6);
        assert_eq!(file.span_text(span), "fungsi");
    }

    #[test]
    fn test_source_map() {
        let mut map = SourceMap::new();
        let id1 = map.add_file("a.rii", "abc");
        let id2 = map.add_file("b.rii", "def");

        assert_eq!(map.file(id1).name(), "a.rii");
        assert_eq!(map.file(id2).name(), "b.rii");
        assert_eq!(map.file_count(), 2);
    }

    #[test]
    fn test_spanned() {
        let spanned = Spanned::new(42, Span::new(0, 2));
        assert_eq!(spanned.value, 42);
        assert_eq!(spanned.span, Span::new(0, 2));

        let mapped = spanned.map(|x| x * 2);
        assert_eq!(mapped.value, 84);
        assert_eq!(mapped.span, Span::new(0, 2));
    }

    #[test]
    fn test_dummy_span() {
        let span = Span::DUMMY;
        assert!(span.is_dummy());
        assert!(span.is_empty());
    }
}
