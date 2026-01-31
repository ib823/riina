// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Bilingual diagnostic rendering for RIINA.
//!
//! Produces error messages in both Bahasa Melayu and English with
//! source spans, underlines, and error codes.

use crate::{FileId, SourceMap, Span};
use core::fmt;
use std::fmt::Write as _;

/// Severity of a diagnostic message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// Fatal error — compilation cannot continue.
    Error,
    /// Non-fatal warning.
    Warning,
    /// Informational note attached to another diagnostic.
    Note,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => write!(f, "ralat/error"),
            Self::Warning => write!(f, "amaran/warning"),
            Self::Note => write!(f, "nota/note"),
        }
    }
}

/// A labeled source location.
#[derive(Debug, Clone)]
pub struct SpannedLabel {
    /// The span in source code.
    pub span: Span,
    /// File this span belongs to.
    pub file_id: FileId,
    /// Label in English.
    pub label_en: String,
    /// Label in Bahasa Melayu.
    pub label_bm: String,
}

/// A bilingual diagnostic message.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Severity level.
    pub severity: Severity,
    /// Error code (e.g., "P0001", "T0003").
    pub code: String,
    /// Message in English.
    pub message_en: String,
    /// Message in Bahasa Melayu.
    pub message_bm: String,
    /// Primary source location.
    pub primary: Option<SpannedLabel>,
    /// Secondary source locations.
    pub secondary: Vec<SpannedLabel>,
    /// Additional notes in English.
    pub notes_en: Vec<String>,
    /// Additional notes in Bahasa Melayu.
    pub notes_bm: Vec<String>,
}

impl Diagnostic {
    /// Create an error diagnostic.
    #[must_use]
    pub fn error(code: impl Into<String>, message_bm: impl Into<String>, message_en: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            code: code.into(),
            message_bm: message_bm.into(),
            message_en: message_en.into(),
            primary: None,
            secondary: Vec::new(),
            notes_en: Vec::new(),
            notes_bm: Vec::new(),
        }
    }

    /// Create a warning diagnostic.
    #[must_use]
    pub fn warning(code: impl Into<String>, message_bm: impl Into<String>, message_en: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            code: code.into(),
            message_bm: message_bm.into(),
            message_en: message_en.into(),
            primary: None,
            secondary: Vec::new(),
            notes_en: Vec::new(),
            notes_bm: Vec::new(),
        }
    }

    /// Set primary span.
    #[must_use]
    pub fn with_primary(mut self, file_id: FileId, span: Span, label_bm: impl Into<String>, label_en: impl Into<String>) -> Self {
        self.primary = Some(SpannedLabel {
            span,
            file_id,
            label_en: label_en.into(),
            label_bm: label_bm.into(),
        });
        self
    }

    /// Add a note.
    #[must_use]
    pub fn with_note(mut self, note_bm: impl Into<String>, note_en: impl Into<String>) -> Self {
        self.notes_bm.push(note_bm.into());
        self.notes_en.push(note_en.into());
        self
    }

    /// Render the diagnostic to a string with source context.
    #[must_use]
    pub fn render(&self, source_map: &SourceMap) -> String {
        let mut out = String::new();

        // Header: severity[code]: message
        let severity_bm = match self.severity {
            Severity::Error => "ralat",
            Severity::Warning => "amaran",
            Severity::Note => "nota",
        };
        let severity_en = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
        };

        let _ = writeln!(out, "{severity_bm}[{}]: {}", self.code, self.message_bm);
        let _ = writeln!(out, "{severity_en}[{}]: {}", self.code, self.message_en);

        // Primary span with source context
        if let Some(ref label) = self.primary {
            if let Some(file) = source_map.get_file(label.file_id) {
                let loc = file.lookup(label.span.start());
                let _ = writeln!(out, "  --> {}:{}:{}", file.name(), loc.line, loc.column);

                // Source line
                let line_text = file.line_text(loc.line);
                if !line_text.is_empty() {
                    let line_num = loc.line.to_string();
                    let pad = " ".repeat(line_num.len());
                    let _ = writeln!(out, "{pad} |");
                    let _ = writeln!(out, "{line_num} | {line_text}");

                    // Underline
                    let col = loc.column as usize;
                    let underline_len = label.span.len().max(1) as usize;
                    // Clamp underline to line length
                    let max_underline = line_text.len().saturating_sub(col.saturating_sub(1));
                    let ul = underline_len.min(max_underline).max(1);
                    let col_pad = " ".repeat(col.saturating_sub(1));
                    let carets = "^".repeat(ul);
                    let _ = writeln!(out, "{pad} | {col_pad}{carets} {}", label.label_bm);
                    let spaces = " ".repeat(ul);
                    let _ = writeln!(out, "{pad} | {col_pad}{spaces} {}", label.label_en);
                }
            }
        }

        // Notes
        for (bm, en) in self.notes_bm.iter().zip(self.notes_en.iter()) {
            let _ = writeln!(out, "  = nota: {bm}");
            let _ = writeln!(out, "  = note: {en}");
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnostic_error_render() {
        let mut sm = SourceMap::new();
        let fid = sm.add_file("test.rii", "biar x = 42;\nbiar y = x + z;\n");

        let diag = Diagnostic::error("T0001", "Pembolehubah tidak ditemui: z", "Variable not found: z")
            .with_primary(fid, Span::new(27, 28), "tidak ditemui", "not found");

        let rendered = diag.render(&sm);
        assert!(rendered.contains("ralat[T0001]"));
        assert!(rendered.contains("error[T0001]"));
        assert!(rendered.contains("test.rii:2:"));
        assert!(rendered.contains("tidak ditemui"));
        assert!(rendered.contains("not found"));
    }

    #[test]
    fn test_diagnostic_with_note() {
        let sm = SourceMap::new();
        let diag = Diagnostic::warning("E0001", "Kesan tidak dibenarkan", "Effect not allowed")
            .with_note("Perlu kesan IO", "Requires IO effect");

        let rendered = diag.render(&sm);
        assert!(rendered.contains("amaran[E0001]"));
        assert!(rendered.contains("Perlu kesan IO"));
        assert!(rendered.contains("Requires IO effect"));
    }
}
