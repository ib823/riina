//! TERAS-LANG Lexer
//!
//! Tokenizes TERAS-LANG source code.
//!
//! Reference: TERAS-LANG-LEXER-SPEC_v1_0_0.md
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

#![forbid(unsafe_code)]
#![deny(clippy::unwrap_used, clippy::expect_used)]
#![warn(clippy::pedantic)]

mod token;
mod lexer;
mod error;

pub use token::{Token, TokenKind, Span};
pub use lexer::Lexer;
pub use error::LexError;
