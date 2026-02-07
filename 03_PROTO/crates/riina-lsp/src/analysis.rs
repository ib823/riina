// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Analysis: parse + typecheck, collect diagnostics.

use riina_parser::Parser;
use riina_typechecker::{type_check, Context};

/// A diagnostic message with position.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub start_line: usize,
    pub start_col: usize,
    pub end_line: usize,
    pub end_col: usize,
    pub severity: DiagnosticSeverity,
}

#[derive(Debug, Clone, Copy)]
pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
}

/// Analyze a source file and return diagnostics.
pub fn analyze(source: &str) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    let mut parser = Parser::new(source);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            let (line, col) = offset_to_line_col(source, e.span.start);
            let (end_line, end_col) = offset_to_line_col(source, e.span.end);
            diagnostics.push(Diagnostic {
                message: e.to_string(),
                start_line: line,
                start_col: col,
                end_line,
                end_col,
                severity: DiagnosticSeverity::Error,
            });
            return diagnostics;
        }
    };

    let expr = program.desugar();
    let ctx = riina_typechecker::register_builtin_types(&Context::new());
    if let Err(e) = type_check(&ctx, &expr) {
        diagnostics.push(Diagnostic {
            message: format!("Type error: {e}"),
            start_line: 0,
            start_col: 0,
            end_line: 0,
            end_col: 0,
            severity: DiagnosticSeverity::Error,
        });
    }

    diagnostics
}

fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 0;
    let mut col = 0;
    for (i, c) in source.char_indices() {
        if i >= offset {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    (line, col)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_analyze_valid() {
        let diags = analyze("biar x = 42; x");
        assert!(diags.is_empty());
    }

    #[test]
    fn test_analyze_parse_error() {
        let diags = analyze("biar = ;");
        assert!(!diags.is_empty());
    }

    #[test]
    fn test_offset_to_line_col() {
        assert_eq!(offset_to_line_col("abc\ndef", 5), (1, 1));
    }
}
