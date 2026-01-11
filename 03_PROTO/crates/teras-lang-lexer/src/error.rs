//! Lexer error types

use std::fmt;

/// Errors that can occur during lexing
#[derive(Debug, Clone)]
pub enum LexError {
    UnexpectedCharacter(char, usize, usize),
    UnterminatedString(usize),
    InvalidEscape(char, usize),
    InvalidNumber(String, usize),
    NotImplemented(&'static str),
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexError::UnexpectedCharacter(c, line, col) => {
                write!(f, "Unexpected character '{}' at line {}, column {}", c, line, col)
            }
            LexError::UnterminatedString(line) => {
                write!(f, "Unterminated string at line {}", line)
            }
            LexError::InvalidEscape(c, line) => {
                write!(f, "Invalid escape sequence '\\{}' at line {}", c, line)
            }
            LexError::InvalidNumber(s, line) => {
                write!(f, "Invalid number '{}' at line {}", s, line)
            }
            LexError::NotImplemented(feature) => {
                write!(f, "Not implemented: {}", feature)
            }
        }
    }
}

impl std::error::Error for LexError {}
