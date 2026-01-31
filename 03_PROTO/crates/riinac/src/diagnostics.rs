//! RIINA Error Diagnostics
//!
//! Provides caret-style error display with source context.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

use riina_lexer::Span;

/// Compute (line, column) from byte offset into source.
/// Both are 1-indexed.
fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Format a diagnostic message with source context, line numbers, and caret.
///
/// Output example:
/// ```text
/// error: Expected type at 12..15
///   --> input.rii:2:5
///   |
/// 2 | biar x: FooBar = 42;
///   |         ^^^^^^
/// ```
pub fn format_diagnostic(source: &str, span: &Span, message: &str, filename: &str) -> String {
    let (line, col) = offset_to_line_col(source, span.start);
    let source_line = source.lines().nth(line - 1).unwrap_or("");
    let underline_len = (span.end - span.start).max(1);

    // Build caret line: spaces up to column, then carets
    let prefix_width = col - 1;
    let carets: String = "^".repeat(underline_len.min(source_line.len().saturating_sub(prefix_width).max(1)));

    let line_num_width = format!("{}", line).len();
    let padding: String = " ".repeat(line_num_width);

    format!(
        "error: {message}\n  --> {filename}:{line}:{col}\n{padding}  |\n{line} | {source_line}\n{padding}  | {spaces}{carets}",
        spaces = " ".repeat(prefix_width),
    )
}
