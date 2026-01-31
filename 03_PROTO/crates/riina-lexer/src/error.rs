// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Lexer Errors

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexError {
    UnexpectedChar(char, usize),
    UnterminatedString(usize),
    UnterminatedChar(usize),
    UnterminatedComment(usize),
    InvalidEscapeSequence(usize),
    InvalidNumericLiteral(String, usize),
    EmptyCharLiteral(usize),
    Unknown(String, usize),
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexError::UnexpectedChar(c, pos) => write!(f, "Unexpected character '{c}' at position {pos}"),
            LexError::UnterminatedString(pos) => write!(f, "Unterminated string starting at position {pos}"),
            LexError::UnterminatedChar(pos) => write!(f, "Unterminated char literal starting at position {pos}"),
            LexError::UnterminatedComment(pos) => write!(f, "Unterminated block comment starting at position {pos}"),
            LexError::InvalidEscapeSequence(pos) => write!(f, "Invalid escape sequence at position {pos}"),
            LexError::InvalidNumericLiteral(s, pos) => write!(f, "Invalid numeric literal '{s}' at position {pos}"),
            LexError::EmptyCharLiteral(pos) => write!(f, "Empty char literal at position {pos}"),
            LexError::Unknown(s, pos) => write!(f, "Unknown error '{s}' at position {pos}"),
        }
    }
}

impl std::error::Error for LexError {}